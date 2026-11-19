use super::{Node, UNBOUNDED, resolve};
use crate::diag::{Diagnostic, Severity};
use crate::syntax::{preprocess::preprocess, railroad::parse};

fn signature(node: &Node) -> String {
    match node {
        Node::Terminal(value) => format!("T({value:?})"),
        Node::NonTerminal(name) => format!("N({name})"),
        Node::Special(text) => format!("S({text:?})"),
        Node::Sequence(elements) => format!("seq[{}]", join_nodes(elements)),
        Node::Choice(alternatives) => format!("ch[{}]", join_nodes(alternatives)),
        Node::Optional(element) => format!("opt({})", signature(element)),
        Node::Repetition { element, min, max } => {
            let max = if *max == UNBOUNDED {
                "inf".to_owned()
            } else {
                max.to_string()
            };
            format!("rep{min}-{max}({})", signature(element))
        }
    }
}

fn join_nodes(nodes: &[Node]) -> String {
    nodes.iter().map(signature).collect::<Vec<_>>().join(" ")
}

fn resolve_source(src: &str) -> (String, Vec<Diagnostic>) {
    let prep = preprocess(src);
    let parsed = parse(src, &prep.removed);
    let (model, resolved) = resolve(&parsed.document);
    let mut out = Vec::new();
    if !model.title.is_empty() {
        out.push(format!("title={:?}", model.title));
    }
    if !model.acc_title.is_empty() {
        out.push(format!("accT={:?}", model.acc_title));
    }
    if !model.acc_descr.is_empty() {
        out.push(format!("accD={:?}", model.acc_descr));
    }
    for rule in &model.rules {
        out.push(format!("{}={}", rule.name, signature(&rule.definition)));
    }
    let mut diagnostics = prep.diagnostics;
    diagnostics.extend(parsed.diagnostics);
    diagnostics.extend(resolved);
    (out.join(" ; "), diagnostics)
}

fn has_error(diagnostics: &[Diagnostic]) -> bool {
    diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
}

fn errors_of(diagnostics: &[Diagnostic]) -> Vec<&Diagnostic> {
    diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect()
}

fn codes(diagnostics: &[&Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(|d| format!("{}@{}-{}", d.code, d.span.start, d.span.end))
        .collect::<Vec<_>>()
        .join(" ")
}

fn span_of(src: &str, text: &str) -> String {
    let start = src.find(text).unwrap_or(0);
    format!("{}-{}", start, start + text.len())
}

const REJECT: &str = "<reject>";

const UPSTREAM_CASES: &[(&str, &str, &str)] = &[
    (
        "constructor entity literal",
        "railroad-beta\nr = terminal(\"a#amp;b\") ;",
        r#"r=T("a#amp;b")"#,
    ),
    (
        "constructor string spans lines",
        "railroad-beta\nr = terminal(\"a\nb\") ;",
        r#"r=T("a\nb")"#,
    ),
    (
        "constructor escaped quote",
        "railroad-beta\nr = terminal(\"a\\\"b\") ;",
        r#"r=T("a\"b")"#,
    ),
    (
        "constructor escaped newline",
        "railroad-beta\nr = terminal('a\\nb') ;",
        r#"r=T("a\nb")"#,
    ),
    (
        "constructor unterminated string",
        "railroad-beta\nr = terminal(\"abc) ;",
        REJECT,
    ),
    (
        "constructor keyword as rule name",
        "railroad-beta\nsequence = terminal(\"a\") ;",
        REJECT,
    ),
    (
        "constructor keyword prefix is an identifier",
        "railroad-beta\nsequencex = terminal(\"a\") ;",
        r#"sequencex=T("a")"#,
    ),
    (
        "title prefix splits an identifier",
        "railroad-beta\ntitles = terminal(\"a\") ;",
        r#"s=T("a")"#,
    ),
    (
        "title",
        "railroad-beta\ntitle Foo\nr = terminal(\"a\") ;",
        r#"title="Foo" ; r=T("a")"#,
    ),
    (
        "title after a rule",
        "railroad-beta\nr = terminal(\"a\") ;\ntitle Foo\n",
        REJECT,
    ),
    (
        "title on the header line",
        "railroad-beta title X\nr = terminal(\"a\") ;",
        r#"title="X" ; r=T("a")"#,
    ),
    (
        "accessibility lines",
        "railroad-beta\naccTitle: T1\naccDescr: D1\nr = terminal(\"a\") ;",
        r#"accT="T1" ; accD="D1" ; r=T("a")"#,
    ),
    (
        "accessibility block",
        "railroad-beta\naccDescr {\n  line1\n\n  line2\n}\nr = terminal(\"a\") ;",
        r#"accD="line1\nline2" ; r=T("a")"#,
    ),
    (
        "accessibility block unterminated",
        "railroad-beta\naccDescr {\nnever closed\nr = terminal(\"a\") ;",
        REJECT,
    ),
    (
        "single-child sequence collapses",
        "railroad-beta\nr = sequence(terminal(\"a\")) ;",
        r#"r=T("a")"#,
    ),
    (
        "single-child choice collapses",
        "railroad-beta\nr = choice(terminal(\"a\")) ;",
        r#"r=T("a")"#,
    ),
    ("empty sequence", "railroad-beta\nr = sequence() ;", REJECT),
    (
        "two rules",
        "railroad-beta\nr = terminal(\"a\") ; q = nonterminal(\"r\") ;",
        r#"r=T("a") ; q=N(r)"#,
    ),
    (
        "duplicate rules stay",
        "railroad-beta\nr = terminal(\"a\") ;\nr = terminal(\"b\") ;",
        r#"r=T("a") ; r=T("b")"#,
    ),
    (
        "trailing percent comment",
        "railroad-beta\nr = terminal(\"a\") ; %% c\n",
        r#"r=T("a")"#,
    ),
    (
        "block comment between tokens",
        "railroad-beta\nr = terminal(\"a\") /* c */ ;",
        r#"r=T("a")"#,
    ),
    (
        "block comment inside call",
        "railroad-beta\nr = terminal(\"a\" /* c */ ) ;",
        r#"r=T("a")"#,
    ),
    ("header only", "railroad-beta\n", ""),
    ("header without newline", "railroad-beta", ""),
    (
        "special",
        "railroad-beta\nr = special(\"x y\") ;",
        r#"r=S("x y")"#,
    ),
    (
        "unquoted argument",
        "railroad-beta\nr = terminal(a) ;",
        REJECT,
    ),
    (
        "junk after the last rule",
        "railroad-beta\nr = terminal(\"a\") ; garbage",
        REJECT,
    ),
    (
        "stray characters",
        "railroad-beta\n@@\nr = terminal(\"a\") ;",
        REJECT,
    ),
    (
        "header comment",
        "railroad-beta %% c\nr = terminal(\"a\") ;",
        r#"r=T("a")"#,
    ),
    (
        "frontmatter",
        "---\ntitle: x\n---\nrailroad-beta\nr = terminal(\"a\") ;",
        r#"r=T("a")"#,
    ),
    (
        "yaml block between rules",
        "railroad-beta\nr = terminal(\"a\") ;\n---\nx\n---\ns = terminal(\"b\") ;",
        r#"r=T("a") ; s=T("b")"#,
    ),
    (
        "title with escapes",
        "railroad-beta\ntitle \"a\\nb\"\nr = terminal(\"a\") ;",
        r#"title="a\nb" ; r=T("a")"#,
    ),
    (
        "title with spaces",
        "railroad-beta\ntitle    spaced     out   \nr = terminal(\"a\") ;",
        r#"title="spaced out" ; r=T("a")"#,
    ),
    (
        "title stops at percent comment",
        "railroad-beta\ntitle A %% c\nr = terminal(\"a\") ;",
        r#"title="A" ; r=T("a")"#,
    ),
    (
        "later description wins",
        "railroad-beta\naccDescr: one  two\naccDescr: later\nr = terminal(\"a\") ;",
        r#"accD="later" ; r=T("a")"#,
    ),
    (
        "inline description block",
        "railroad-beta\naccDescr{ a\n b }\nr = terminal(\"a\") ;",
        r#"accD="a\nb" ; r=T("a")"#,
    ),
    (
        "description block after a newline",
        "railroad-beta\naccDescr\n{ a }\nr = terminal(\"a\") ;",
        r#"accD="a" ; r=T("a")"#,
    ),
    (
        "accTitle collapses blanks",
        "railroad-beta\naccTitle : T  1 \nr = terminal(\"a\") ;",
        r#"accT="T 1" ; r=T("a")"#,
    ),
    (
        "empty title",
        "railroad-beta\ntitle\nr = terminal(\"a\") ;",
        r#"r=T("a")"#,
    ),
    (
        "later empty title wins",
        "railroad-beta title A\ntitle\nr = terminal(\"a\") ;",
        r#"r=T("a")"#,
    ),
    (
        "escaped backslash",
        "railroad-beta\nr = terminal(\"a\\\\\") ;",
        r#"r=T("a\\")"#,
    ),
    (
        "unknown escape drops the backslash",
        "railroad-beta\nr = terminal(\"a\\q\") ;",
        r#"r=T("aq")"#,
    ),
    (
        "empty terminal",
        "railroad-beta\nr = terminal(\"\") ;",
        r#"r=T("")"#,
    ),
    (
        "header with a dot",
        "railroad-beta.x\nr = terminal(\"a\") ;",
        REJECT,
    ),
    (
        "header reused as a rule name",
        "railroad-beta\nrailroad-beta = terminal(\"a\") ;",
        REJECT,
    ),
    (
        "ebnf equals",
        "railroad-ebnf-beta\nr = \"a\" \"b\" ;",
        r#"r=seq[T("a") T("b")]"#,
    ),
    (
        "ebnf bare terms",
        "railroad-ebnf-beta\nr = a b c ;",
        "r=seq[N(a) N(b) N(c)]",
    ),
    (
        "ebnf colon equals",
        "railroad-ebnf-beta\nr ::= a, b | c ;",
        "r=ch[seq[N(a) N(b)] N(c)]",
    ),
    ("ebnf lone colon", "railroad-ebnf-beta\nr : \"a\" ;", REJECT),
    (
        "ebnf colon-equals typo",
        "railroad-ebnf-beta\nr := a ;",
        REJECT,
    ),
    (
        "ebnf postfix question",
        "railroad-ebnf-beta\nr = a ? ;",
        "r=opt(N(a))",
    ),
    (
        "ebnf special beats question",
        "railroad-ebnf-beta\nr = a? , b? ;",
        r#"r=seq[N(a) S(", b")]"#,
    ),
    (
        "ebnf special after question",
        "railroad-ebnf-beta\nr = a ? b ? ;",
        r#"r=seq[N(a) S("b")]"#,
    ),
    (
        "ebnf special",
        "railroad-ebnf-beta\nr = ? x ? ;",
        r#"r=S("x")"#,
    ),
    (
        "ebnf blank special",
        "railroad-ebnf-beta\nr = ?   ? ;",
        REJECT,
    ),
    (
        "ebnf iso comment",
        "railroad-ebnf-beta\nr = a (* c *) b ;",
        "r=seq[N(a) N(b)]",
    ),
    (
        "ebnf slash comment",
        "railroad-ebnf-beta\nr = a /* c */ b ;",
        "r=seq[N(a) N(b)]",
    ),
    (
        "ebnf unclosed iso comment",
        "railroad-ebnf-beta\nr = a (* unclosed b ;",
        REJECT,
    ),
    (
        "ebnf exception",
        "railroad-ebnf-beta\nr = (a | b)* - c ;",
        r#"r=seq[rep0-inf(ch[N(a) N(b)]) T("-") N(c)]"#,
    ),
    (
        "ebnf chained exception",
        "railroad-ebnf-beta\nr = a - b - c ;",
        r#"r=seq[seq[N(a) T("-") N(b)] T("-") N(c)]"#,
    ),
    (
        "ebnf postfix chain",
        "railroad-ebnf-beta\nr = a*+? ;",
        "r=opt(rep1-inf(rep0-inf(N(a))))",
    ),
    (
        "ebnf group forms",
        "railroad-ebnf-beta\nr = [a] {b} (c) ;",
        "r=seq[opt(N(a)) rep0-inf(N(b)) N(c)]",
    ),
    (
        "ebnf double bar",
        "railroad-ebnf-beta\nr = a | | b ;",
        REJECT,
    ),
    ("ebnf empty body", "railroad-ebnf-beta\nr = ;", REJECT),
    (
        "ebnf alternatives and next rule",
        "railroad-ebnf-beta\nr = \"a\" , \"b\" | 'c' ;\ns = r ;",
        r#"r=ch[seq[T("a") T("b")] T("c")] ; s=N(r)"#,
    ),
    (
        "ebnf rule on one line",
        "railroad-ebnf-beta\nr ::= a ; s = b ;",
        "r=N(a) ; s=N(b)",
    ),
    (
        "ebnf hyphenated identifier",
        "railroad-ebnf-beta\nr = a-b ;",
        "r=N(a-b)",
    ),
    (
        "ebnf spaced exception",
        "railroad-ebnf-beta\nr = a - b ;",
        r#"r=seq[N(a) T("-") N(b)]"#,
    ),
    (
        "ebnf unspaced exception",
        "railroad-ebnf-beta\nr = a -b ;",
        r#"r=seq[N(a) T("-") N(b)]"#,
    ),
    (
        "ebnf trailing comma",
        "railroad-ebnf-beta\nr = a, ;",
        REJECT,
    ),
    (
        "ebnf unclosed group",
        "railroad-ebnf-beta\nr = (a ;",
        REJECT,
    ),
    (
        "ebnf yaml block",
        "railroad-ebnf-beta\nr = a ;\n---\nx\n---\ns = b ;",
        "r=N(a) ; s=N(b)",
    ),
    (
        "abnf finite repeat",
        "railroad-abnf-beta\nr = 1*3a ;",
        "r=rep1-3(N(a))",
    ),
    (
        "abnf repeat forms",
        "railroad-abnf-beta\nr = 2a 3\"b\" *c 0*1d 1*e 3*2f ;",
        r#"r=seq[rep2-2(N(a)) rep3-3(T("b")) rep0-inf(N(c)) opt(N(d)) rep1-inf(N(e)) rep3-2(N(f))]"#,
    ),
    (
        "abnf numeric values",
        "railroad-abnf-beta\nr = %x41 %x41-5A %x41.42.43 %d65 %b1010 ;",
        r#"r=seq[T("%x41") T("%x41-5A") T("%x41.42.43") T("%d65") T("%b1010")]"#,
    ),
    (
        "abnf alternation",
        "railroad-abnf-beta\nr = a / b c / d ;",
        "r=ch[N(a) seq[N(b) N(c)] N(d)]",
    ),
    (
        "abnf backslash stays",
        "railroad-abnf-beta\nr = \"a\\b\" ;",
        r#"r=T("a\\b")"#,
    ),
    (
        "abnf comment line between rules",
        "railroad-abnf-beta\nr = a ;\n; comment\ns = b ;",
        "r=N(a) ; s=N(b)",
    ),
    (
        "abnf terminator on its own line",
        "railroad-abnf-beta\nr = a\n  ;\ns = b ;",
        "r=N(a) ; s=N(b)",
    ),
    (
        "abnf crlf",
        "railroad-abnf-beta\nr = a ;\r\ns = b ;",
        "r=N(a) ; s=N(b)",
    ),
    (
        "abnf groups",
        "railroad-abnf-beta\nr = ( a / b ) [ c ] ;",
        "r=seq[ch[N(a) N(b)] opt(N(c))]",
    ),
    (
        "abnf repeat on groups",
        "railroad-abnf-beta\nr = 1*(a) 2[b] ;",
        "r=seq[rep1-inf(N(a)) rep2-2(opt(N(b)))]",
    ),
    (
        "abnf numval stops at a non-hex digit",
        "railroad-abnf-beta\nr = %x4G ;",
        r#"r=seq[T("%x4") N(G)]"#,
    ),
    (
        "abnf zero maximum",
        "railroad-abnf-beta\nr = 0*0a ;",
        "r=rep0-0(N(a))",
    ),
    (
        "abnf bare star",
        "railroad-abnf-beta\nr = *a ;",
        "r=rep0-inf(N(a))",
    ),
    (
        "abnf leading zeros",
        "railroad-abnf-beta\nr = 007*0009 a ;",
        "r=rep7-9(N(a))",
    ),
    (
        "abnf comment after terminator",
        "railroad-abnf-beta\nr = \"a\" ; \nq = \"b\" ; x\n",
        REJECT,
    ),
    (
        "abnf comment swallows the next line start",
        "railroad-abnf-beta\nr = \"a\" ; c\nq = \"b\" ;\n",
        REJECT,
    ),
    (
        "abnf title keeps backslashes",
        "railroad-abnf-beta\ntitle \"a\\nb\"\nr = a ;",
        r#"title="a\\nb" ; r=N(a)"#,
    ),
    ("peg rule", "railroad-peg-beta\nr <- a ;", "r=N(a)"),
    (
        "peg predicates and suffixes",
        "railroad-peg-beta\nr <- &a b !c d? e* f+ ;",
        r#"r=seq[S("&a") N(b) S("!c") opt(N(d)) rep0-inf(N(e)) rep1-inf(N(f))]"#,
    ),
    (
        "peg lookahead labels",
        "railroad-peg-beta\nr <- &(a / b) !\"x\" &. ;",
        r#"r=seq[S("&(...)") S("!\"x\"") S("&.")]"#,
    ),
    (
        "peg group suffix",
        "railroad-peg-beta\nr <- (a b)+ / c ;",
        "r=ch[rep1-inf(seq[N(a) N(b)]) N(c)]",
    ),
    ("peg any", "railroad-peg-beta\nr <- . ;", r#"r=S(".")"#),
    (
        "peg comment",
        "railroad-peg-beta\nr <- a # comment\n b ;",
        "r=seq[N(a) N(b)]",
    ),
    ("peg double prefix", "railroad-peg-beta\nr <- &&a ;", REJECT),
    ("peg double suffix", "railroad-peg-beta\nr <- a?* ;", REJECT),
    ("peg wrong arrow", "railroad-peg-beta\nr = a ;", REJECT),
    ("peg empty body", "railroad-peg-beta\nr <- ;", REJECT),
    (
        "peg title escapes",
        "railroad-peg-beta\ntitle \"a\\tb\"\nr <- a ;",
        r#"title="a\tb" ; r=N(a)"#,
    ),
];

#[test]
fn matches_upstream() {
    for (name, src, want) in UPSTREAM_CASES {
        let (got, diagnostics) = resolve_source(src);
        if *want == REJECT {
            assert!(
                has_error(&diagnostics),
                "{name}: accepted, want a rejection; model {got}"
            );
            continue;
        }
        assert!(
            !has_error(&diagnostics),
            "{name}: rejected: {diagnostics:?}"
        );
        assert_eq!(&got, want, "{name}");
    }
}

#[test]
fn no_rules_warning() {
    let (_, diagnostics) = resolve_source("railroad-beta\ntitle Empty");
    let refs: Vec<&Diagnostic> = diagnostics.iter().collect();
    assert_eq!(codes(&refs), "railroad/no-rules@0-13");
    assert_eq!(diagnostics[0].severity, Severity::Warning);
}

#[test]
fn repeat_maximum_notice() {
    let src = "railroad-abnf-beta\nr = 1*3a 0*1b *c 2d ;";
    let (_, diagnostics) = resolve_source(src);
    let got: Vec<String> = diagnostics
        .iter()
        .map(|d| {
            format!(
                "{}|{}|{:?}|{}-{}",
                d.code, d.message, d.severity, d.span.start, d.span.end
            )
        })
        .collect();
    let exact = src.find("2d").unwrap_or(0);
    let want = [
        format!(
            "railroad/repeat-max-ignored|finite repetition maximum 3 is not drawn|Info|{}",
            span_of(src, "1*3")
        ),
        format!(
            "railroad/repeat-max-ignored|finite repetition maximum 2 is not drawn|Info|{}-{}",
            exact,
            exact + 1
        ),
    ];
    assert_eq!(got, want);
}

#[test]
fn recovery_keeps_later_rules() {
    let (got, diagnostics) = resolve_source(
        "railroad-beta\nbad = sequence( ;\nr = terminal(\"a\") ;\nbad2 = terminal(a) ;\ns = terminal(\"b\") ;",
    );
    assert_eq!(got, r#"r=T("a") ; s=T("b")"#);
    let names: Vec<&str> = diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(
        names,
        ["railroad/unexpected-token", "railroad/unexpected-token"]
    );
}

#[test]
fn unknown_statements() {
    let src = "railroad-beta\nr = terminal(\"a\") ;\naccTitle: x\n= ;\ns = terminal(\"b\") ;";
    let (_, diagnostics) = resolve_source(src);
    let want = format!(
        "railroad/unknown-statement@{} railroad/unknown-statement@{}",
        span_of(src, "accTitle: x"),
        span_of(src, "= ;")
    );
    assert_eq!(codes(&errors_of(&diagnostics)), want);
    assert_eq!(diagnostics[0].message, "unknown statement accTitle: x");
}

#[test]
fn unterminated_names() {
    let cases = [
        ("railroad-beta\nr = terminal(\"abc", "\""),
        ("railroad-beta\nr = terminal('abc", "'"),
        ("railroad-beta\nr = /* abc", "/*"),
        ("railroad-beta\naccDescr {\nabc", "{"),
        ("railroad-abnf-beta\nr = \"abc", "\""),
    ];
    for (src, opener) in cases {
        let (_, diagnostics) = resolve_source(src);
        let errors = errors_of(&diagnostics);
        assert_eq!(errors.len(), 1, "{src:?}: {}", codes(&errors));
        assert_eq!(errors[0].code, "railroad/unterminated", "{src:?}");
        assert_eq!(
            errors[0].message,
            format!("unterminated {opener}"),
            "{src:?}"
        );
        assert_eq!(errors[0].span.end, src.len(), "{src:?}");
    }
}

#[test]
fn unexpected_token_lists_sorted_kinds() {
    let cases = [
        (
            "railroad-beta\nr = ;",
            "unexpected ;, expected one of: choice, nonterminal, oneOrMore, optional, sequence, special, terminal, zeroOrMore",
        ),
        (
            "railroad-peg-beta\nr = a ;",
            "unexpected =, expected one of: <-",
        ),
        (
            "railroad-ebnf-beta\nr = a",
            "unexpected EOF, expected one of: ;",
        ),
        (
            "railroad-ebnf-beta\nr =",
            "unexpected EOF, expected one of: (, EBNF_ID, EBNF_SPECIAL_SEQUENCE, EBNF_STRING, [, {",
        ),
    ];
    for (src, want) in cases {
        let (_, diagnostics) = resolve_source(src);
        let errors = errors_of(&diagnostics);
        assert_eq!(errors.len(), 1, "{src:?}");
        assert_eq!(errors[0].message, want, "{src:?}");
    }
}

#[test]
fn nesting_limit() {
    let deep = |levels: usize| {
        format!(
            "railroad-beta\nr = {}terminal(\"a\"){} ;",
            "optional(".repeat(levels),
            ")".repeat(levels)
        )
    };
    let (_, diagnostics) = resolve_source(&deep(64));
    assert!(
        !has_error(&diagnostics),
        "64 levels rejected: {diagnostics:?}"
    );
    let (_, diagnostics) = resolve_source(&deep(65));
    let errors = errors_of(&diagnostics);
    assert!(
        errors.len() == 1 && errors[0].code == "limit/nesting-depth",
        "65 levels: {}",
        codes(&errors)
    );
    let postfix = format!("railroad-ebnf-beta\nr = a{} ;", "*+".repeat(33));
    let (_, diagnostics) = resolve_source(&postfix);
    let errors = errors_of(&diagnostics);
    assert!(
        errors.len() == 1 && errors[0].code == "limit/nesting-depth",
        "66 postfix levels: {}",
        codes(&errors)
    );
    let groups = format!(
        "railroad-ebnf-beta\nr = {}a{} ;",
        "(".repeat(65),
        ")".repeat(65)
    );
    let (_, diagnostics) = resolve_source(&groups);
    let errors = errors_of(&diagnostics);
    assert!(
        errors.len() == 1 && errors[0].code == "limit/nesting-depth",
        "65 groups: {}",
        codes(&errors)
    );
}

#[test]
fn header_case_folds() {
    for header in ["RAILROAD-BETA", "Railroad-Beta"] {
        let (got, diagnostics) = resolve_source(&format!("{header}\nr = terminal(\"a\") ;"));
        assert!(
            !has_error(&diagnostics) && got == r#"r=T("a")"#,
            "{header}: {got} {diagnostics:?}"
        );
    }
}
