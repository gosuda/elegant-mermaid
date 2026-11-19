//! Recursive-descent parser for the wardley grammar (`spec/grammar/wardley.md`).

use crate::diag::Diagnostic;
use crate::source::Span;

use super::ast::{
    Accelerator, Anchor, Annotation, Annotations, Component, Decorator, Evolution, EvolutionStage,
    Evolve, Label, Link, Metadata, Note, Pipeline, PipelineComponent, Size, Value, Wardley,
};
use super::lexer::{Token, lex};
use super::{C_UNEXPECTED, C_UNKNOWN, C_UNTERMINATED, diagnostic};

const NAME_KINDS: &[&str] = &["ID", "NAME_WITH_SPACES", "STRING"];
const COORDINATE: &[&str] = &["INT", "WARDLEY_NUMBER"];
const DECIMAL: &[&str] = &["WARDLEY_NUMBER"];
const INTEGER: &[&str] = &["INT"];

pub struct Parsed {
    pub document: Wardley,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str, removed: &[Span]) -> Parsed {
    let mut parser = Parser {
        source,
        tokens: lex(source, removed),
        at: 0,
        openers: Vec::new(),
        diagnostics: Vec::new(),
        out: Wardley {
            span: Span { start: 0, end: 0 },
            header: None,
            metadata: Vec::new(),
            size: None,
            evolution: None,
            anchors: Vec::new(),
            components: Vec::new(),
            links: Vec::new(),
            evolves: Vec::new(),
            pipelines: Vec::new(),
            notes: Vec::new(),
            annotations: Vec::new(),
            annotation: Vec::new(),
            accelerators: Vec::new(),
            deaccelerators: Vec::new(),
        },
    };
    parser.skip_newlines();
    parser.header();
    parser.statements();
    let start = parser.out.header.as_ref().map_or(0, |t| t.span.start);
    parser.out.span = Span {
        start,
        end: source.len(),
    };
    Parsed {
        document: parser.out,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    at: usize,
    openers: Vec<Token>,
    diagnostics: Vec<Diagnostic>,
    out: Wardley,
}

fn with(expected: &[&'static str], more: &[&'static str]) -> Vec<&'static str> {
    expected.iter().chain(more).copied().collect()
}

impl Parser<'_> {
    fn eof(&self) -> Token {
        Token {
            kind: "EOF",
            text: String::new(),
            span: Span {
                start: self.source.len(),
                end: self.source.len(),
            },
        }
    }

    fn token(&self) -> Token {
        self.tokens
            .get(self.at)
            .cloned()
            .unwrap_or_else(|| self.eof())
    }

    fn kind(&self) -> &'static str {
        self.tokens.get(self.at).map_or("EOF", |t| t.kind)
    }

    fn peek_kind(&self, ahead: usize) -> &'static str {
        self.tokens.get(self.at + ahead).map_or("EOF", |t| t.kind)
    }

    fn take(&mut self) -> Token {
        let token = self.token();
        if self.at < self.tokens.len() {
            self.at += 1;
        }
        token
    }

    fn skip_newlines(&mut self) {
        while self.kind() == "NEWLINE" {
            self.at += 1;
        }
    }

    fn span(&self, start: usize) -> Span {
        let end = self
            .at
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or(start, |t| t.span.end);
        Span { start, end }
    }

    fn raw(&self, span: Span) -> &str {
        self.source.get(span.start..span.end).unwrap_or("")
    }

    fn issue(&mut self, code: &'static str, message: String, span: Span) {
        self.diagnostics.push(diagnostic(code, message, span));
    }

    fn unexpected(&mut self, expected: &[&str]) {
        let token = self.token();
        if token.kind == "UNTERMINATED" {
            return;
        }
        if let (true, Some(opener)) = (token.kind == "EOF", self.openers.last()) {
            let message = format!("unterminated {}", opener.text);
            let span = Span {
                start: opener.span.start,
                end: self.source.len(),
            };
            self.issue(C_UNTERMINATED, message, span);
            return;
        }
        let mut names = expected.to_vec();
        names.sort_unstable();
        let message = format!(
            "unexpected {}, expected one of: {}",
            self.raw(token.span),
            names.join(", ")
        );
        self.issue(C_UNEXPECTED, message, token.span);
    }

    fn line_end(&self) -> usize {
        self.tokens
            .iter()
            .skip(self.at)
            .find(|t| matches!(t.kind, "NEWLINE" | "EOF" | "UNTERMINATED"))
            .map_or(self.source.len(), |t| t.span.start)
    }

    fn skip_line(&mut self) {
        self.skip_until(&[]);
    }

    fn skip_member_line(&mut self) {
        self.skip_until(&["}"]);
    }

    fn skip_until(&mut self, stops: &[&str]) {
        loop {
            let kind = self.kind();
            if matches!(kind, "EOF" | "UNTERMINATED") || stops.contains(&kind) {
                return;
            }
            if kind == "NEWLINE" {
                self.take();
                return;
            }
            self.take();
        }
    }

    fn header(&mut self) {
        if self.kind() != "KW_WARDLEY" {
            self.unexpected(&["KW_WARDLEY"]);
            return;
        }
        self.out.header = Some(self.take());
    }

    fn statements(&mut self) {
        loop {
            match self.kind() {
                "EOF" => return,
                "UNTERMINATED" => {
                    let token = self.token();
                    let message = format!("unterminated {}", token.text);
                    self.issue(C_UNTERMINATED, message, token.span);
                    return;
                }
                "NEWLINE" => {
                    self.take();
                }
                _ => self.statement(),
            }
        }
    }

    fn dispatch(&mut self, kind: &str) -> Option<bool> {
        Some(match kind {
            "KW_SIZE" => self.size(),
            "KW_EVOLUTION" => self.evolution(),
            "KW_ANCHOR" => self.anchor(),
            "KW_COMPONENT" => self.component(),
            "KW_EVOLVE" => self.evolve(),
            "KW_PIPELINE" => self.pipeline(),
            "KW_NOTE" => self.note(),
            "KW_ANNOTATIONS" => self.annotations(),
            "KW_ANNOTATION" => self.annotation(),
            "KW_ACCELERATOR" => self.accelerator(),
            "KW_DEACCELERATOR" => self.deaccelerator(),
            "ID" | "NAME_WITH_SPACES" | "STRING" => self.link(),
            "ACC_DESCR" | "ACC_TITLE" | "TITLE" => self.metadata(),
            _ => return None,
        })
    }

    fn statement(&mut self) {
        let first = self.token();
        let base = self.openers.len();
        let Some(ok) = self.dispatch(first.kind) else {
            let message = format!("unknown statement {}", self.raw(first.span));
            let span = Span {
                start: first.span.start,
                end: self.line_end().max(first.span.end),
            };
            self.issue(C_UNKNOWN, message, span);
            self.skip_line();
            return;
        };
        self.openers.truncate(base);
        if !ok {
            self.skip_line();
        }
    }

    fn eol(&mut self, expected: &[&'static str]) -> bool {
        match self.kind() {
            "NEWLINE" => {
                self.skip_newlines();
                true
            }
            "EOF" => true,
            _ => {
                self.unexpected(&with(expected, &["EOF", "NEWLINE"]));
                false
            }
        }
    }

    fn field(&mut self, kinds: &[&str]) -> Option<Value> {
        if !kinds.contains(&self.kind()) {
            self.unexpected(kinds);
            return None;
        }
        Some(Value::of(self.take()))
    }

    fn name(&mut self, extra: &[&'static str]) -> Option<Value> {
        self.field(&with(extra, NAME_KINDS))
    }

    fn punct(&mut self, kind: &'static str) -> Option<()> {
        if self.kind() != kind {
            self.unexpected(&[kind]);
            return None;
        }
        self.take();
        Some(())
    }

    fn opener(&mut self, kind: &'static str) -> Option<()> {
        if self.kind() != kind {
            self.unexpected(&[kind]);
            return None;
        }
        let token = self.take();
        self.openers.push(token);
        Some(())
    }

    fn closer(&mut self, kind: &'static str) -> Option<()> {
        self.punct(kind)?;
        self.openers.pop();
        Some(())
    }

    fn pair(&mut self, kinds: &[&str]) -> Option<(Value, Value)> {
        self.opener("[")?;
        let x = self.field(kinds)?;
        self.punct(",")?;
        let y = self.field(kinds)?;
        self.closer("]")?;
        Some((x, y))
    }

    fn size(&mut self) -> bool {
        let start = self.take().span.start;
        let Some(node) = self.size_node(start) else {
            return false;
        };
        self.out.size = Some(node);
        self.eol(&[])
    }

    fn size_node(&mut self, start: usize) -> Option<Size> {
        self.opener("[")?;
        let width = self.field(INTEGER)?;
        self.punct(",")?;
        let height = self.field(INTEGER)?;
        self.closer("]")?;
        Some(Size {
            span: self.span(start),
            width,
            height,
        })
    }

    fn evolution(&mut self) -> bool {
        let start = self.take().span.start;
        let mut stages = Vec::new();
        loop {
            let Some((stage, follow)) = self.stage() else {
                return false;
            };
            stages.push(stage);
            if self.kind() != "ARROW" {
                return self.finish_evolution(stages, start, follow);
            }
            self.take();
        }
    }

    fn finish_evolution(
        &mut self,
        stages: Vec<EvolutionStage>,
        start: usize,
        follow: Vec<&'static str>,
    ) -> bool {
        let expected = with(&follow, &["ARROW"]);
        if stages.len() < 2 {
            self.unexpected(&expected);
            return false;
        }
        self.out.evolution = Some(Evolution {
            span: self.span(start),
            stages,
        });
        self.eol(&expected)
    }

    fn stage(&mut self) -> Option<(EvolutionStage, Vec<&'static str>)> {
        let name = self.name(&[])?;
        let mut follow = vec!["@", "/"];
        let mut boundary = None;
        let mut second_name = None;
        if self.kind() == "@" {
            self.take();
            boundary = Some(self.field(DECIMAL)?);
            follow.remove(0);
        }
        if self.kind() == "/" {
            self.take();
            second_name = Some(self.name(&[])?);
            follow.clear();
        }
        let end = self.tokens.get(self.at.checked_sub(1)?)?.span.end;
        let span = Span {
            start: name.span.start,
            end,
        };
        Some((
            EvolutionStage {
                span,
                name,
                boundary,
                second_name,
            },
            follow,
        ))
    }

    fn anchor(&mut self) -> bool {
        let start = self.take().span.start;
        let Some(node) = self.anchor_node(start) else {
            return false;
        };
        self.out.anchors.push(node);
        self.eol(&[])
    }

    fn anchor_node(&mut self, start: usize) -> Option<Anchor> {
        let name = self.name(&[])?;
        let (visibility, evolution) = self.pair(DECIMAL)?;
        Some(Anchor {
            span: self.span(start),
            name,
            visibility,
            evolution,
        })
    }

    fn label(&mut self) -> Option<Label> {
        let start = self.take().span.start;
        self.opener("[")?;
        let (neg_x, offset_x) = self.signed()?;
        self.punct(",")?;
        let (neg_y, offset_y) = self.signed()?;
        self.closer("]")?;
        Some(Label {
            span: self.span(start),
            neg_x,
            offset_x,
            neg_y,
            offset_y,
        })
    }

    fn signed(&mut self) -> Option<(bool, Value)> {
        let negative = self.kind() == "-";
        if negative {
            self.take();
        }
        Some((negative, self.field(INTEGER)?))
    }

    fn component(&mut self) -> bool {
        let start = self.take().span.start;
        let Some(name) = self.name(&[]) else {
            return false;
        };
        let Some((visibility, evolution)) = self.pair(DECIMAL) else {
            return false;
        };
        let mut node = Component {
            span: Span { start, end: start },
            name,
            visibility,
            evolution,
            label: None,
            decorator: None,
            inertia: false,
        };
        let Some(follow) = self.component_tail(&mut node) else {
            return false;
        };
        node.span = self.span(start);
        self.out.components.push(node);
        self.eol(&follow)
    }

    fn component_tail(&mut self, node: &mut Component) -> Option<Vec<&'static str>> {
        let mut follow = vec!["(", "KW_INERTIA", "KW_LABEL"];
        if self.kind() == "KW_LABEL" {
            node.label = Some(self.label()?);
            follow.truncate(2);
        }
        if self.kind() == "(" && self.peek_kind(1) != "KW_INERTIA" {
            node.decorator = Some(self.decorator()?);
        }
        match self.kind() {
            "KW_INERTIA" => {
                self.take();
                node.inertia = true;
                Some(Vec::new())
            }
            "(" => {
                node.inertia = true;
                self.inertia_group()?;
                Some(Vec::new())
            }
            _ => Some(follow),
        }
    }

    fn decorator(&mut self) -> Option<Decorator> {
        let start = self.token().span.start;
        self.opener("(")?;
        let strategy = self.field(&["STRATEGY"])?;
        self.closer(")")?;
        Some(Decorator {
            span: self.span(start),
            strategy,
        })
    }

    fn inertia_group(&mut self) -> Option<()> {
        self.opener("(")?;
        self.punct("KW_INERTIA")?;
        self.closer(")")
    }

    fn link(&mut self) -> bool {
        let start = self.token().span.start;
        let Some(node) = self.link_node(start) else {
            return false;
        };
        let trailing = if node.to_port.is_some() {
            vec!["LINK_LABEL"]
        } else {
            vec!["LINK_LABEL", "LINK_PORT"]
        };
        let expected: &[&'static str] = if node.link_label.is_some() {
            &[]
        } else {
            &trailing
        };
        self.out.links.push(node);
        self.eol(expected)
    }

    fn link_node(&mut self, start: usize) -> Option<Link> {
        let from = self.name(&[]).unwrap_or_else(Value::empty);
        let mut follow = vec!["ARROW", "LINK_ARROW", "LINK_PORT"];
        let mut from_port = None;
        let mut arrow = None;
        if self.kind() == "LINK_PORT" {
            from_port = Some(Value::of(self.take()));
            follow.truncate(2);
        }
        if matches!(self.kind(), "LINK_ARROW" | "ARROW") {
            arrow = Some(Value::of(self.take()));
            follow.clear();
        }
        let to = self.name(&follow)?;
        let mut to_port = None;
        let mut link_label = None;
        if self.kind() == "LINK_PORT" {
            to_port = Some(Value::of(self.take()));
        }
        if self.kind() == "LINK_LABEL" {
            link_label = Some(Value::of(self.take()));
        }
        Some(Link {
            span: self.span(start),
            from,
            from_port,
            arrow,
            to,
            to_port,
            link_label,
        })
    }

    fn evolve(&mut self) -> bool {
        let start = self.take().span.start;
        let Some(component) = self.name(&[]) else {
            return false;
        };
        let Some(target) = self.field(DECIMAL) else {
            return false;
        };
        self.out.evolves.push(Evolve {
            span: self.span(start),
            component,
            target,
        });
        self.eol(&[])
    }

    fn pipeline(&mut self) -> bool {
        let start = self.take().span.start;
        let Some(parent) = self.name(&[]) else {
            return false;
        };
        if self.opener("{").is_none() {
            return false;
        }
        if self.kind() != "NEWLINE" {
            self.unexpected(&["NEWLINE"]);
            return false;
        }
        self.skip_newlines();
        let Some(components) = self.members() else {
            return false;
        };
        if components.is_empty() {
            self.unexpected(&["KW_COMPONENT"]);
            return false;
        }
        let _ = self.closer("}");
        self.out.pipelines.push(Pipeline {
            span: self.span(start),
            parent,
            components,
        });
        self.eol(&[])
    }

    fn members(&mut self) -> Option<Vec<PipelineComponent>> {
        let mut components = Vec::new();
        loop {
            match self.kind() {
                "}" => return Some(components),
                "NEWLINE" => {
                    self.take();
                }
                "KW_COMPONENT" => self.member(&mut components)?,
                _ => {
                    self.unexpected(&["KW_COMPONENT", "}"]);
                    if matches!(self.kind(), "EOF" | "UNTERMINATED") {
                        return None;
                    }
                    self.skip_member_line();
                }
            }
        }
    }

    fn member(&mut self, components: &mut Vec<PipelineComponent>) -> Option<()> {
        let base = self.openers.len();
        let child = self.pipeline_component();
        self.openers.truncate(base);
        if let Some(child) = child {
            components.push(child);
            return Some(());
        }
        if matches!(self.kind(), "EOF" | "UNTERMINATED") {
            return None;
        }
        self.skip_member_line();
        Some(())
    }

    fn pipeline_component(&mut self) -> Option<PipelineComponent> {
        let start = self.take().span.start;
        let name = self.name(&[])?;
        self.opener("[")?;
        let evolution = self.field(DECIMAL)?;
        self.closer("]")?;
        let mut follow: &[&'static str] = &["KW_LABEL"];
        let mut label = None;
        if self.kind() == "KW_LABEL" {
            label = Some(self.label()?);
            follow = &[];
        }
        let node = PipelineComponent {
            span: self.span(start),
            name,
            evolution,
            label,
        };
        self.eol(follow).then_some(node)
    }

    fn note(&mut self) -> bool {
        let start = self.take().span.start;
        let Some(text) = self.field(&["STRING"]) else {
            return false;
        };
        let Some((visibility, evolution)) = self.pair(DECIMAL) else {
            return false;
        };
        self.out.notes.push(Note {
            span: self.span(start),
            text,
            visibility,
            evolution,
        });
        self.eol(&[])
    }

    fn annotations(&mut self) -> bool {
        let start = self.take().span.start;
        let Some((x, y)) = self.pair(COORDINATE) else {
            return false;
        };
        self.out.annotations.push(Annotations {
            span: self.span(start),
            x,
            y,
        });
        self.eol(&[])
    }

    fn annotation(&mut self) -> bool {
        let start = self.take().span.start;
        let Some(node) = self.annotation_node(start) else {
            return false;
        };
        self.out.annotation.push(node);
        self.eol(&[])
    }

    fn annotation_node(&mut self, start: usize) -> Option<Annotation> {
        let number = self.field(INTEGER)?;
        self.punct(",")?;
        let (x, y) = self.pair(COORDINATE)?;
        let text = self.field(&["STRING"])?;
        Some(Annotation {
            span: self.span(start),
            number,
            x,
            y,
            text,
        })
    }

    fn force_statement(&mut self) -> Option<Accelerator> {
        let start = self.take().span.start;
        let name = self.name(&[])?;
        let (x, y) = self.pair(DECIMAL)?;
        Some(Accelerator {
            span: self.span(start),
            name,
            x,
            y,
        })
    }

    fn accelerator(&mut self) -> bool {
        let Some(node) = self.force_statement() else {
            return false;
        };
        self.out.accelerators.push(node);
        self.eol(&[])
    }

    fn deaccelerator(&mut self) -> bool {
        let Some(node) = self.force_statement() else {
            return false;
        };
        self.out.deaccelerators.push(node);
        self.eol(&[])
    }

    fn metadata(&mut self) -> bool {
        let token = self.take();
        let field = match token.kind {
            "ACC_DESCR" => "accDescr",
            "ACC_TITLE" => "accTitle",
            _ => "title",
        };
        self.out.metadata.push(Metadata {
            field,
            value: token.text,
            span: token.span,
        });
        self.eol(&[])
    }
}
