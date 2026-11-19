//! Resolved treeview declarations, including the synthetic directory root.
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::syntax::config_value::ConfigValue;
use crate::syntax::preprocess::preprocess;
use crate::syntax::treeview::{ast::TreeView, diagnostic};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub index: usize,
    pub parent: Option<usize>,
    pub level: i64,
    pub depth: usize,
    pub children: Vec<usize>,
    pub name: String,
    pub directory: bool,
    pub icon: String,
    pub class: String,
    pub description: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Config {
    pub row_indent: Option<i32>,
    pub padding_x: Option<i32>,
    pub padding_y: Option<i32>,
    pub line_thickness: Option<i32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Model {
    pub nodes: Vec<Node>,
    pub config: Config,
    pub title: String,
    pub acc_title: String,
    pub acc_descr: String,
}

fn value(token: &Option<crate::syntax::treeview::ast::Token>) -> String {
    token
        .as_ref()
        .map_or_else(String::new, |token| token.value.clone())
}

pub fn resolve(source: &str, document: &TreeView) -> (Model, Vec<Diagnostic>) {
    let model = Model {
        config: read_config(source),
        title: value(&document.title),
        acc_title: value(&document.acc_title),
        acc_descr: value(&document.acc_descr),
        nodes: vec![Node {
            index: 0,
            parent: None,
            level: -1,
            depth: 0,
            children: Vec::new(),
            name: "/".into(),
            directory: true,
            icon: String::new(),
            class: String::new(),
            description: String::new(),
            span: Span { start: 0, end: 0 },
        }],
    };
    let mut resolver = Resolver {
        model,
        stack: vec![0],
        diagnostics: Vec::new(),
        too_deep: false,
    };
    for ast in &document.nodes {
        resolver.insert(ast);
    }
    (resolver.model, resolver.diagnostics)
}

struct Resolver {
    model: Model,
    stack: Vec<usize>,
    diagnostics: Vec<Diagnostic>,
    too_deep: bool,
}

impl Resolver {
    fn insert(&mut self, ast: &crate::syntax::treeview::ast::TreeNode) {
        let level = ast.indent.as_ref().map_or(0, |token| token.text.len());
        let level = i64::try_from(level).unwrap_or(i64::MAX);
        while self.stack.len() > 1
            && self
                .stack
                .last()
                .is_some_and(|i| level <= self.model.nodes[*i].level)
        {
            self.stack.pop();
        }
        let parent = self.stack.last().copied().unwrap_or(0);
        let index = self.model.nodes.len();
        let depth = self.model.nodes[parent].depth + 1;
        let mut icon = value(&ast.icon);
        if ast.icon.is_some() && icon.is_empty() {
            icon = "none".into();
        }
        self.model.nodes[parent].children.push(index);
        self.model.nodes.push(Node {
            index,
            parent: Some(parent),
            level,
            depth,
            children: Vec::new(),
            name: ast
                .name
                .value
                .strip_suffix('/')
                .unwrap_or(&ast.name.value)
                .to_owned(),
            directory: ast.name.value.ends_with('/'),
            icon,
            class: value(&ast.class),
            description: value(&ast.desc),
            span: ast.span,
        });
        self.stack.push(index);
        self.check_depth(depth, ast.span);
    }

    fn check_depth(&mut self, depth: usize, span: Span) {
        if depth <= 64 || self.too_deep {
            return;
        }
        self.too_deep = true;
        let mut note = diagnostic(
            "limit/nesting-depth",
            "nesting depth exceeds 64".into(),
            span,
        );
        note.help = "Reduce the nesting to 64 levels or fewer.".into();
        self.diagnostics.push(note);
    }
}

fn read_config(source: &str) -> Config {
    let pre = preprocess(source);
    let mut config = Config::default();
    for block in [pre.frontmatter.and_then(|f| f.config), pre.init_config]
        .into_iter()
        .flatten()
    {
        let ConfigValue::Mapping(entries) = block else {
            continue;
        };
        let Some(entry) = entries.iter().find(|entry| entry.key == "treeView") else {
            continue;
        };
        let ConfigValue::Mapping(fields) = &entry.value else {
            continue;
        };
        for field in fields {
            let Some(value) =
                crate::syntax::config_value::thousandths(&field.value).filter(|v| *v >= 0)
            else {
                continue;
            };
            let target = match field.key.as_str() {
                "rowIndent" => &mut config.row_indent,
                "paddingX" => &mut config.padding_x,
                "paddingY" => &mut config.padding_y,
                "lineThickness" => &mut config.line_thickness,
                _ => continue,
            };
            *target = Some(value);
        }
    }
    config
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn treeview_semantics_keep_annotations_and_directory_suffix() {
        let source = "treeView-beta\n a// :::highlight icon() ## note\n    child\n b\n";
        let parsed = crate::syntax::treeview::parse(source, &[]);
        assert!(parsed.diagnostics.is_empty());
        let (model, diagnostics) = resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
        let node = &model.nodes[1];
        assert_eq!(
            (
                node.name.as_str(),
                node.directory,
                node.icon.as_str(),
                node.class.as_str(),
                node.description.as_str()
            ),
            ("a/", true, "none", "highlight", "note")
        );
        assert_eq!(model.nodes[2].parent, Some(1));
        assert_eq!(model.nodes[3].parent, Some(0));
    }

    #[test]
    fn treeview_nesting_limit_counts_parent_chain_not_spaces() {
        let mut source = String::from("treeView-beta\n");
        for depth in 1..=65 {
            source.push_str(&" ".repeat(depth));
            source.push_str("node\n");
        }
        let parsed = crate::syntax::treeview::parse(&source, &[]);
        let (_, diagnostics) = resolve(&source, &parsed.document);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "limit/nesting-depth");
        let source = "treeView-beta\n a\n                                                                b\n";
        let parsed = crate::syntax::treeview::parse(source, &[]);
        let (_, diagnostics) = resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn treeview_init_config_overrides_frontmatter() {
        let source = "---\nconfig:\n  treeView:\n    rowIndent: 2\n---\n%%{init: {\"treeView\": {\"rowIndent\": 7.5}}}%%\ntreeView-beta\n a\n";
        let pre = preprocess(source);
        let parsed = crate::syntax::treeview::parse(source, &pre.removed);
        let (model, diagnostics) = resolve(source, &parsed.document);
        assert!(diagnostics.is_empty());
        assert_eq!(model.config.row_indent, Some(7500));
    }
}
