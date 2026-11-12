use crate::diag::{Diagnostic, Severity};
use crate::source::Span;
use crate::syntax::config_value::{
    ConfigValue, ParsedDoc, parse_json_doc, parse_yaml_doc, token_span,
};
use crate::syntax::{eol_len, line_content_end};

/// Code for every preprocessing diagnostic (preprocessing-126 to preprocessing-129).
pub const C_MALFORMED: &str = "config/malformed";

/// One recognized `%%{...}%%` directive, in source order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Directive {
    pub name: String,
    pub body: Span,
    pub init: Option<ConfigValue>,
    pub wrap: bool,
}

/// The frontmatter block: body span, parsed value, and extracted `config` mapping.
#[derive(Debug, Clone)]
pub struct Frontmatter {
    pub body: Span,
    pub value: ConfigValue,
    pub config: Option<ConfigValue>,
}

/// The result of preprocessing one source text (spec/preprocessing.md).
#[derive(Debug, Clone)]
pub struct Preprocessed {
    pub frontmatter: Option<Frontmatter>,
    pub directives: Vec<Directive>,
    pub init_config: Option<ConfigValue>,
    pub wrap: bool,
    pub removed: Vec<Span>,
    pub diagnostics: Vec<Diagnostic>,
}

/// Splits frontmatter, directives, and `%%` comments out of src; spans never change.
pub fn preprocess(src: &str) -> Preprocessed {
    let mut p = Prep {
        src,
        b: src.as_bytes(),
        region: 0,
        wrap: false,
        init: None,
        directives: Vec::new(),
        diags: Vec::new(),
        spans: Vec::new(),
        frontmatter: None,
    };
    p.frontmatter();
    p.directive_scan();
    p.comment_scan();
    p.merge_init();
    Preprocessed {
        frontmatter: p.frontmatter.take(),
        directives: std::mem::take(&mut p.directives),
        init_config: p.init.take().map(ConfigValue::Mapping),
        wrap: p.wrap,
        removed: merge_spans(std::mem::take(&mut p.spans)),
        diagnostics: std::mem::take(&mut p.diags),
    }
}

struct Fence {
    start: usize,
    end: usize,
}

struct Prep<'a> {
    src: &'a str,
    b: &'a [u8],
    region: usize,
    wrap: bool,
    init: Option<Vec<Entry>>,
    directives: Vec<Directive>,
    diags: Vec<Diagnostic>,
    spans: Vec<Span>,
    frontmatter: Option<Frontmatter>,
}

use crate::syntax::config_value::Entry;

impl<'a> Prep<'a> {
    fn frontmatter(&mut self) {
        let Some(f) = fence_at(self.b, 0) else {
            return;
        };
        let Some(c) = closing_fence(self.b, f.end) else {
            return;
        };
        let body = Span {
            start: f.end,
            end: c.start,
        };
        let doc = parse_yaml_doc(self.src, body.start, body.end);
        let config = self.front_config(&doc, body);
        self.diags.extend(doc.diagnostics);
        self.spans.push(Span {
            start: 0,
            end: c.end,
        });
        self.frontmatter = Some(Frontmatter {
            body,
            value: doc.value,
            config,
        });
        self.region = c.end;
    }

    fn front_config(&mut self, doc: &ParsedDoc, body: Span) -> Option<ConfigValue> {
        let ConfigValue::Mapping(entries) = &doc.value else {
            return None;
        };
        let e = entries.iter().find(|e| e.key == "config")?;
        match &e.value {
            ConfigValue::Mapping(_) => Some(e.value.clone()),
            _ => {
                let at = doc
                    .starts
                    .iter()
                    .find(|(k, _)| k == "config")
                    .map(|(_, v)| *v)
                    .unwrap_or(body.end);
                let span = token_span(self.src, body.start, body.end, at);
                self.push_malformed("frontmatter config must be a mapping", span);
                None
            }
        }
    }

    fn directive_scan(&mut self) {
        let len = self.b.len();
        let mut p = self.region;
        while p < len {
            if is_dir_start(self.b, p) {
                let end = self.directive(p).max(p + 1);
                self.spans.push(Span { start: p, end });
                p = end;
            } else {
                p += 1;
            }
        }
    }

    fn directive(&mut self, p: usize) -> usize {
        let Some(cj) = self.dir_close(p) else {
            self.push_malformed(
                "malformed directive",
                Span {
                    start: p,
                    end: p + 3,
                },
            );
            return self.b.len();
        };
        let after = self.dir_ws(p + 3, cj);
        let (name, name_end) = self.dir_word(after, cj);
        let colon = self.dir_ws(name_end, cj);
        if !matches!(name.as_str(), "init" | "initialize" | "wrap") {
            return cj + 3;
        }
        if colon < cj && self.b.get(colon) == Some(&b':') {
            return self.directive_body(p, cj, colon, name);
        }
        if colon != cj {
            self.push_malformed(
                "malformed directive",
                Span {
                    start: p,
                    end: p + 3,
                },
            );
            return cj + 3;
        }
        let wrap = name == "wrap";
        self.directives.push(Directive {
            name,
            body: Span { start: cj, end: cj },
            init: None,
            wrap,
        });
        cj + 3
    }

    fn directive_body(&mut self, p: usize, cj: usize, colon: usize, name: String) -> usize {
        if name == "wrap" {
            self.push_malformed(
                "wrap takes no body",
                Span {
                    start: p,
                    end: p + 3,
                },
            );
            return cj + 3;
        }
        let mut d = Directive {
            name,
            body: Span {
                start: colon + 1,
                end: cj,
            },
            init: None,
            wrap: false,
        };
        self.init_body(&mut d);
        self.directives.push(d);
        cj + 3
    }

    fn init_body(&mut self, d: &mut Directive) {
        let (s, e) = (d.body.start, d.body.end);
        let Some(q) = self.first_non_ws(s, e) else {
            return;
        };
        if self.b.get(q) != Some(&b'{') {
            let span = token_span(self.src, s, e, q);
            self.push_malformed("directive body must be a JSON object", span);
            return;
        }
        let jd = parse_json_doc(self.src, s, e);
        self.diags.extend(jd.diagnostics);
        if !jd.stop {
            d.init = Some(jd.value);
        }
    }

    fn dir_close(&self, p: usize) -> Option<usize> {
        let len = self.b.len();
        let mut j = p + 3;
        while j + 2 < len {
            if matches!(
                (self.b.get(j), self.b.get(j + 1), self.b.get(j + 2)),
                (Some(b'}'), Some(b'%'), Some(b'%'))
            ) {
                return Some(j);
            }
            j += 1;
        }
        None
    }

    fn dir_ws(&self, from: usize, to: usize) -> usize {
        let mut i = from;
        while i < to
            && matches!(
                self.b.get(i),
                Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
            )
        {
            i += 1;
        }
        i
    }

    fn dir_word(&self, from: usize, to: usize) -> (String, usize) {
        let mut i = from;
        while i < to && matches!(self.b.get(i), Some(c) if c.is_ascii_alphanumeric() || *c == b'_')
        {
            i += 1;
        }
        (self.src.get(from..i).unwrap_or_default().to_string(), i)
    }

    fn first_non_ws(&self, from: usize, to: usize) -> Option<usize> {
        let mut i = from;
        while i < to
            && matches!(
                self.b.get(i),
                Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
            )
        {
            i += 1;
        }
        (i < to).then_some(i)
    }

    fn comment_scan(&mut self) {
        let len = self.b.len();
        let mut p = self.region;
        while p < len {
            let e = line_content_end(self.b, p, len);
            if self.comment_line(p, e) {
                self.spans.push(Span {
                    start: p,
                    end: e + eol_len(self.b, e),
                });
            }
            let nl = e + eol_len(self.b, e);
            if nl <= p {
                break;
            }
            p = nl;
        }
    }

    fn comment_line(&self, ls: usize, e: usize) -> bool {
        let mut i = ls;
        while i < e && matches!(self.b.get(i), Some(b' ') | Some(b'\t')) {
            i += 1;
        }
        if !matches!((self.b.get(i), self.b.get(i + 1)), (Some(b'%'), Some(b'%'))) {
            return false;
        }
        self.b.get(i + 2) != Some(&b'{')
    }

    fn merge_init(&mut self) {
        let dirs = std::mem::take(&mut self.directives);
        let mut acc: Option<Vec<Entry>> = None;
        for d in &dirs {
            if d.wrap {
                self.wrap = true;
            }
            let Some(ConfigValue::Mapping(add)) = &d.init else {
                continue;
            };
            acc = Some(match acc.take() {
                None => add.clone(),
                Some(base) => merge_top(&base, add),
            });
        }
        self.directives = dirs;
        self.init = acc;
    }

    fn push_malformed(&mut self, msg: &str, span: Span) {
        self.diags.push(Diagnostic {
            code: C_MALFORMED,
            severity: Severity::Error,
            message: msg.to_string(),
            span,
            related: Vec::new(),
            help: String::new(),
            fixes: Vec::new(),
        });
    }
}

fn fence_at(b: &[u8], from: usize) -> Option<Fence> {
    let mut i = from;
    while matches!(b.get(i), Some(b' ') | Some(b'\t')) {
        i += 1;
    }
    if !matches!(
        (b.get(i), b.get(i + 1), b.get(i + 2)),
        (Some(b'-'), Some(b'-'), Some(b'-'))
    ) {
        return None;
    }
    let mut j = i + 3;
    while matches!(b.get(j), Some(b' ') | Some(b'\t')) {
        j += 1;
    }
    let e = line_content_end(b, j, b.len());
    if e != j {
        return None;
    }
    let el = eol_len(b, e);
    if el == 0 {
        return None;
    }
    Some(Fence {
        start: from,
        end: e + el,
    })
}

fn closing_fence(b: &[u8], mut from: usize) -> Option<Fence> {
    while from < b.len() {
        if let Some(f) = fence_at(b, from) {
            return Some(f);
        }
        let e = line_content_end(b, from, b.len());
        if e >= b.len() {
            return None;
        }
        from = e + eol_len(b, e);
    }
    None
}

fn is_dir_start(b: &[u8], p: usize) -> bool {
    matches!(
        (b.get(p), b.get(p + 1), b.get(p + 2)),
        (Some(b'%'), Some(b'%'), Some(b'{'))
    )
}

fn merge_spans(mut spans: Vec<Span>) -> Vec<Span> {
    spans.sort_by_key(|s| s.start);
    let mut out: Vec<Span> = Vec::new();
    for s in spans {
        match out.last_mut() {
            Some(l) if s.start < l.end => {
                if s.end > l.end {
                    l.end = s.end;
                }
            }
            _ => out.push(s),
        }
    }
    out
}

fn merge_top(base: &[Entry], add: &[Entry]) -> Vec<Entry> {
    let mut out = base.to_vec();
    for e in add {
        match out.iter_mut().find(|x| x.key == e.key) {
            Some(slot) => slot.value = merged_value(&slot.value, &e.value),
            None => out.push(e.clone()),
        }
    }
    out
}

fn merged_value(a: &ConfigValue, b: &ConfigValue) -> ConfigValue {
    let (ConfigValue::Mapping(ma), ConfigValue::Mapping(mb)) = (a, b) else {
        return b.clone();
    };
    ConfigValue::Mapping(merge_one(ma, mb))
}

fn merge_one(base: &[Entry], add: &[Entry]) -> Vec<Entry> {
    let mut out = base.to_vec();
    for e in add {
        match out.iter_mut().find(|x| x.key == e.key) {
            Some(slot) => slot.value = e.value.clone(),
            None => out.push(e.clone()),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(ds: &[Diagnostic], code: &str, msg: &str, span: Span) {
        let [d] = ds else { unreachable!() };
        assert_eq!(d.code, code);
        assert_eq!(d.message, msg);
        assert_eq!(d.span, span);
        assert_eq!(d.severity, Severity::Error);
        assert!(d.help.is_empty());
    }

    fn sequence(v: ConfigValue) -> Vec<ConfigValue> {
        let ConfigValue::Sequence(s) = v else {
            unreachable!()
        };
        s
    }

    fn same_shape(a: &ConfigValue, b: &ConfigValue) -> bool {
        match (a, b) {
            (ConfigValue::Mapping(ma), ConfigValue::Mapping(mb)) => {
                ma.len() == mb.len()
                    && ma
                        .iter()
                        .zip(mb)
                        .all(|(x, y)| x.key == y.key && same_shape(&x.value, &y.value))
            }
            (ConfigValue::Sequence(sa), ConfigValue::Sequence(sb)) => {
                sa.len() == sb.len() && sa.iter().zip(sb).all(|(x, y)| same_shape(x, y))
            }
            _ => a == b,
        }
    }

    fn cfg_of(p: &Preprocessed) -> ConfigValue {
        let Some(f) = &p.frontmatter else {
            unreachable!()
        };
        let Some(c) = &f.config else { unreachable!() };
        c.clone()
    }

    fn str_map(pairs: &[(&str, &str)]) -> Vec<Entry> {
        pairs
            .iter()
            .map(|(k, v)| Entry {
                key: String::from(*k),
                key_span: Span { start: 0, end: 0 },
                value: ConfigValue::String(String::from(*v)),
            })
            .collect()
    }

    const ALPHABET: [char; 25] = [
        ' ', '\t', '\n', ':', '-', '#', '[', ']', '{', '}', ',', '\'', '"', '|', '>', '&', '*',
        '!', 'a', 'b', 'c', '0', '1', '2', '\\',
    ];

    struct Xs(u32);

    impl Xs {
        fn next(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u32) -> u32 {
            self.next() % n
        }
    }

    fn random_case(i: u32) -> String {
        let mut g = Xs(i.wrapping_add(1));
        let len = 1 + g.below(40);
        let mut s = String::new();
        for _ in 0..len {
            let idx = g.below(25) as usize;
            let Some(c) = ALPHABET.get(idx) else {
                unreachable!()
            };
            s.push(*c);
        }
        s
    }

    fn in_bounds(s: &str, sp: Span) -> bool {
        sp.start <= sp.end
            && sp.end <= s.len()
            && s.is_char_boundary(sp.start)
            && s.is_char_boundary(sp.end)
    }

    #[test]
    fn no_fence_and_unterminated_fence() {
        let p = preprocess("flowchart TD\n");
        assert!(p.frontmatter.is_none());
        assert!(p.removed.is_empty());
        assert!(p.diagnostics.is_empty());
        let p = preprocess("---\na: 1\n");
        assert!(p.frontmatter.is_none());
        assert!(p.removed.is_empty());
        let p = preprocess("--- x\na: 1\n");
        assert!(p.frontmatter.is_none());
        let p = preprocess("----\na: 1\n");
        assert!(p.frontmatter.is_none());
    }

    #[test]
    fn fence_shapes_and_line_endings() {
        let p = preprocess("---\nconfig:\n  theme: dark\n---\nA");
        let Some(f) = &p.frontmatter else {
            unreachable!()
        };
        assert_eq!(f.body, Span { start: 4, end: 26 });
        assert!(same_shape(
            &cfg_of(&p),
            &ConfigValue::Mapping(str_map(&[("theme", "dark")]))
        ));
        assert_eq!(p.removed, vec![Span { start: 0, end: 30 }]);
        assert!(p.diagnostics.is_empty());

        let p = preprocess("  --- \na: 1\n  ---\nB");
        let Some(f) = &p.frontmatter else {
            unreachable!()
        };
        assert_eq!(f.body, Span { start: 7, end: 12 });
        assert_eq!(p.removed, vec![Span { start: 0, end: 18 }]);

        let p = preprocess("---\r\nconfig: {a: 1}\r\n---\r\nA");
        let want = ConfigValue::Mapping(vec![Entry {
            key: String::from("a"),
            key_span: Span { start: 0, end: 0 },
            value: ConfigValue::Integer(String::from("1")),
        }]);
        assert!(same_shape(&cfg_of(&p), &want));
        assert_eq!(p.removed, vec![Span { start: 0, end: 26 }]);

        let p = preprocess("---\ra: 1\r---\rB");
        let Some(f) = &p.frontmatter else {
            unreachable!()
        };
        assert_eq!(f.body, Span { start: 4, end: 9 });
        assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);
        assert!(p.diagnostics.is_empty());
    }

    #[test]
    fn frontmatter_roots_without_config() {
        let p = preprocess("---\nhello\n---\nA");
        let Some(f) = &p.frontmatter else {
            unreachable!()
        };
        assert_eq!(f.value, ConfigValue::String(String::from("hello")));
        assert!(f.config.is_none());
        assert!(p.diagnostics.is_empty());

        let p = preprocess("---\n[1, 2]\n---\nA");
        let Some(f) = &p.frontmatter else {
            unreachable!()
        };
        assert_eq!(sequence(f.value.clone()).len(), 2);
        assert!(f.config.is_none());
        assert!(p.diagnostics.is_empty());

        let p = preprocess("---\n---\nA");
        let Some(f) = &p.frontmatter else {
            unreachable!()
        };
        assert_eq!(f.body, Span { start: 4, end: 4 });
        assert_eq!(f.value, ConfigValue::Null);
        assert!(f.config.is_none());
        assert_eq!(p.removed, vec![Span { start: 0, end: 8 }]);
    }

    #[test]
    fn frontmatter_config_must_be_mapping_span() {
        let p = preprocess("---\nconfig: 42\n---\nA\n");
        check(
            &p.diagnostics,
            C_MALFORMED,
            "frontmatter config must be a mapping",
            Span { start: 12, end: 14 },
        );
        assert!(p.frontmatter.as_ref().is_none_or(|f| f.config.is_none()));
    }

    #[test]
    fn unknown_directives_removed_silently() {
        let p = preprocess("%%{foo bar}%%\nA\n");
        assert!(p.diagnostics.is_empty());
        assert!(p.directives.is_empty());
        assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);

        let p = preprocess("%%{}%%\nA");
        assert!(p.diagnostics.is_empty());
        assert!(p.directives.is_empty());

        let p = preprocess("%%{initx: 1}%%\nA");
        assert!(p.diagnostics.is_empty());
        assert!(p.directives.is_empty());
    }

    #[test]
    fn malformed_directive_forms() {
        let p = preprocess("%%{init x}%%\n");
        check(
            &p.diagnostics,
            C_MALFORMED,
            "malformed directive",
            Span { start: 0, end: 3 },
        );
        assert!(p.directives.is_empty());
        assert_eq!(p.removed, vec![Span { start: 0, end: 12 }]);

        let p = preprocess("%%{init: {\n");
        check(
            &p.diagnostics,
            C_MALFORMED,
            "malformed directive",
            Span { start: 0, end: 3 },
        );
        assert_eq!(p.removed, vec![Span { start: 0, end: 11 }]);

        let p = preprocess("%%{wrap: x}%%\n");
        check(
            &p.diagnostics,
            C_MALFORMED,
            "wrap takes no body",
            Span { start: 0, end: 3 },
        );
        assert!(p.directives.is_empty());
        assert!(!p.wrap);
        assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);

        let p = preprocess("%%{init: 1}%%\n");
        check(
            &p.diagnostics,
            C_MALFORMED,
            "directive body must be a JSON object",
            Span { start: 9, end: 10 },
        );
        assert_eq!(p.removed, vec![Span { start: 0, end: 13 }]);
    }

    #[test]
    fn known_directives_without_effect() {
        let p = preprocess("%%{init}%%\n");
        assert!(p.diagnostics.is_empty());
        let [d] = p.directives.as_slice() else {
            unreachable!()
        };
        assert_eq!(d.name, "init");
        assert!(d.init.is_none());
        assert!(!d.wrap);
        assert_eq!(p.removed, vec![Span { start: 0, end: 10 }]);

        let p = preprocess("%%{init: }%%\n");
        assert!(p.diagnostics.is_empty());
        let [d] = p.directives.as_slice() else {
            unreachable!()
        };
        assert!(d.init.is_none());
        assert_eq!(d.body, Span { start: 8, end: 9 });

        let p = preprocess("%%{initialize}%%\nA");
        assert!(p.diagnostics.is_empty());
        let [d] = p.directives.as_slice() else {
            unreachable!()
        };
        assert_eq!(d.name, "initialize");
    }

    #[test]
    fn wrap_directive_sets_flag() {
        let p = preprocess("%%{wrap}%%\nB");
        assert!(p.diagnostics.is_empty());
        assert!(p.wrap);
        let [d] = p.directives.as_slice() else {
            unreachable!()
        };
        assert_eq!(d.name, "wrap");
        assert!(d.wrap);
        assert_eq!(d.body, Span { start: 7, end: 7 });
        assert_eq!(p.removed, vec![Span { start: 0, end: 10 }]);
    }

    #[test]
    fn init_bodies_merge_to_depth_two() {
        let src = "%%{init: {'a': {'x': 1, 'y': 2}}}%%%%{init: {'a': {'y': 3}, 'b': 4}}%%\nZ";
        let p = preprocess(src);
        assert!(p.diagnostics.is_empty());
        assert_eq!(p.directives.len(), 2);
        let Some(merged) = &p.init_config else {
            unreachable!()
        };
        let want = ConfigValue::Mapping(vec![
            Entry {
                key: String::from("a"),
                key_span: Span { start: 0, end: 0 },
                value: ConfigValue::Mapping(vec![
                    Entry {
                        key: String::from("x"),
                        key_span: Span { start: 0, end: 0 },
                        value: ConfigValue::Integer(String::from("1")),
                    },
                    Entry {
                        key: String::from("y"),
                        key_span: Span { start: 0, end: 0 },
                        value: ConfigValue::Integer(String::from("3")),
                    },
                ]),
            },
            Entry {
                key: String::from("b"),
                key_span: Span { start: 0, end: 0 },
                value: ConfigValue::Integer(String::from("4")),
            },
        ]);
        assert!(same_shape(merged, &want));
    }

    #[test]
    fn init_config_key_stays_ordinary() {
        let src = "%%{init: {'config': {'x': 1}}}%%\n";
        let p = preprocess(src);
        assert!(p.diagnostics.is_empty());
        let Some(merged) = &p.init_config else {
            unreachable!()
        };
        let ConfigValue::Mapping(m) = merged else {
            unreachable!()
        };
        assert_eq!(m.len(), 1);
        assert_eq!(m[0].key, "config");
    }

    #[test]
    fn comment_lines_removed_and_directives_inside_them_apply() {
        let p = preprocess("%% hi\nA\n");
        assert!(p.diagnostics.is_empty());
        assert_eq!(p.removed, vec![Span { start: 0, end: 6 }]);

        let src = "%% x %%{init: {'t': 1}}%%\nA\n";
        let p = preprocess(src);
        assert!(p.diagnostics.is_empty());
        assert_eq!(p.directives.len(), 1);
        assert_eq!(p.removed, vec![Span { start: 0, end: 26 }]);
    }

    #[test]
    fn frontmatter_removed_before_directive_scan() {
        let src = "---\n%%{init: 1}%%\n---\n%%{wrap}%%\nA\n";
        let p = preprocess(src);
        assert!(p.wrap);
        assert_eq!(p.directives.len(), 1);
        assert!(p.diagnostics.is_empty());
        assert!(!p.removed.iter().any(|s| s.start == 4));
    }

    #[test]
    fn removed_spans_stay_sorted_and_disjoint() {
        let src = "---\n%% x\n---\n%% y\n%%{wrap}%%\nA\n";
        let p = preprocess(src);
        assert!(p.wrap);
        let starts: Vec<usize> = p.removed.iter().map(|s| s.start).collect();
        let mut sorted = starts.clone();
        sorted.sort();
        assert_eq!(starts, sorted);
        for w in p.removed.windows(2) {
            assert!(w[1].start >= w[0].end, "overlap {w:?}");
        }
    }

    #[test]
    fn diagnostics_propagate_from_frontmatter_body() {
        let src = "---\n\ta: 1\n---\nA\n";
        let p = preprocess(src);
        check(
            &p.diagnostics,
            C_MALFORMED,
            "tab in indentation",
            Span { start: 4, end: 5 },
        );
    }

    #[test]
    fn random_spans_stay_in_range() {
        for i in 0u32..2000 {
            let s = random_case(i);
            let p = preprocess(&s);
            for d in &p.diagnostics {
                assert!(
                    in_bounds(&s, d.span),
                    "case {i} diag {:?} src {s:?}",
                    d.span
                );
            }
            for sp in &p.removed {
                assert!(in_bounds(&s, *sp), "case {i} removed {:?} src {s:?}", sp);
            }
            for d in &p.directives {
                assert!(
                    in_bounds(&s, d.body),
                    "case {i} body {:?} src {s:?}",
                    d.body
                );
            }
        }
    }
}
