use super::Model;
use crate::diag::{Diagnostic, Severity};
use crate::source::Span;
use crate::syntax::flowchart::ast::ClickAction;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClickLink {
    pub target: String,
    pub url: String,
    pub tooltip: Option<String>,
}

const NO_SPAN: Span = Span { start: 0, end: 0 };

pub(super) fn resolve(source: &str, model: &mut Model) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut links: Vec<ClickLink> = Vec::new();
    for click in &model.clicks {
        match &click.action {
            ClickAction::Call {
                name, name_span, ..
            }
            | ClickAction::PlainCall {
                name, name_span, ..
            } => {
                if !name.is_empty() {
                    diagnostics.push(callback_ignored(name, *name_span));
                }
            }
            ClickAction::Link {
                href,
                href_span,
                tooltip,
                ..
            } => {
                if *href_span == NO_SPAN {
                    continue;
                }
                if crate::interaction::SafeUrl::new(href).is_none() {
                    diagnostics.push(unsafe_url(*href_span));
                }
                let target = source
                    .get(click.target.start..click.target.end)
                    .unwrap_or("")
                    .trim()
                    .to_owned();
                let link = ClickLink {
                    target,
                    url: href.clone(),
                    tooltip: tooltip.clone(),
                };
                match links.iter_mut().find(|l| l.target == link.target) {
                    Some(existing) => *existing = link,
                    None => links.push(link),
                }
            }
        }
    }
    model.links = links;
    diagnostics
}

fn callback_ignored(name: &str, span: Span) -> Diagnostic {
    crate::syntax::flowchart::diagnostic(
        "interaction/callback-ignored",
        Severity::Info,
        format!("callback {name} is ignored"),
        span,
    )
}

fn unsafe_url(span: Span) -> Diagnostic {
    crate::syntax::flowchart::diagnostic(
        "interaction/unsafe-url",
        Severity::Warning,
        "link URL is not allowed".into(),
        span,
    )
}

#[cfg(test)]
mod tests {
    use crate::{
        Diagnostic, RenderError, Severity, SvgOptions, TextOptions, parse, render_svg, render_text,
    };

    const BASE: &str = "flowchart LR\n  A[Start] --> B[End]\n";

    fn with(clicks: &str) -> String {
        format!("{BASE}{clicks}")
    }

    fn notes<'a>(diagnostics: &'a [Diagnostic], code: &str) -> Vec<&'a Diagnostic> {
        diagnostics.iter().filter(|d| d.code == code).collect()
    }

    #[test]
    fn interaction_unsafe_url() -> Result<(), RenderError> {
        for href in [
            "javascript:alert(1)",
            "JavaScript:alert(1)",
            "data:text/html,x",
            "/relative/path",
            "example.test",
            "ftp://example.test",
            "",
        ] {
            let source = with(&format!("  click A \"{href}\" \"tip\"\n"));
            let document = parse(&source);
            let found = notes(document.diagnostics(), "interaction/unsafe-url");
            assert_eq!(found.len(), 1, "{href:?}: {:?}", document.diagnostics());
            let note = found[0];
            assert_eq!(note.severity, Severity::Warning);
            assert_eq!(note.message, "link URL is not allowed");
            assert_eq!(note.help, "Use an http, https, or mailto link.");
            assert_eq!(
                &source[note.span.start..note.span.end],
                format!("\"{href}\"")
            );
            assert!(!document.has_errors(), "{:?}", document.diagnostics());
            let svg = render_svg(&document, &SvgOptions::default())?;
            assert!(!svg.contains("<a "), "{href:?}: {svg}");
            assert!(!svg.contains("javascript"), "{href:?}");
        }
        Ok(())
    }

    #[test]
    fn interaction_safe_links_wrap_their_node_in_an_anchor() -> Result<(), RenderError> {
        let source = with(
            "  click A \"https://example.test/a?x=1&y=2\" \"Open A\"\n  click B href \" MAILTO:me@example.test \"\n",
        );
        let document = parse(&source);
        assert!(
            notes(document.diagnostics(), "interaction/unsafe-url").is_empty(),
            "{:?}",
            document.diagnostics()
        );
        let svg = render_svg(&document, &SvgOptions::default())?;
        assert!(
            svg.contains(
                "<a href='https://example.test/a?x=1&amp;y=2'>\n<title>Open A</title>\n<g class='emd-node'"
            ),
            "{svg}"
        );
        assert!(
            svg.contains("<a href='MAILTO:me@example.test'>\n<g class='emd-node'"),
            "{svg}"
        );
        assert_eq!(svg.matches("<a ").count(), 2, "{svg}");
        assert_eq!(svg.matches("</a>").count(), 2, "{svg}");
        Ok(())
    }

    #[test]
    fn interaction_last_click_for_a_target_wins_and_unknown_targets_draw_nothing()
    -> Result<(), RenderError> {
        let source = with(
            "  click A \"https://first.test\"\n  click A \"https://second.test\"\n  click Z \"https://absent.test\"\n",
        );
        let svg = render_svg(&parse(&source), &SvgOptions::default())?;
        assert!(svg.contains("https://second.test"), "{svg}");
        assert!(!svg.contains("first.test"), "{svg}");
        assert!(!svg.contains("absent.test"), "{svg}");
        let superseded = with("  click A \"javascript:x\"\n  click A \"https://second.test\"\n");
        let document = parse(&superseded);
        assert_eq!(
            notes(document.diagnostics(), "interaction/unsafe-url").len(),
            1,
            "a superseded unsafe URL still warns"
        );
        assert!(render_svg(&document, &SvgOptions::default())?.contains("https://second.test"));
        Ok(())
    }

    #[test]
    fn interaction_callbacks_are_ignored_with_an_info() -> Result<(), RenderError> {
        let source = with(
            "  click A call handler(1, 2) \"tip\"\n  click B plainHandler \"tip\"\n  click A call other()\n",
        );
        let document = parse(&source);
        let found = notes(document.diagnostics(), "interaction/callback-ignored");
        let messages: Vec<_> = found.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(
            messages,
            [
                "callback handler is ignored",
                "callback plainHandler is ignored",
                "callback other is ignored"
            ]
        );
        for note in &found {
            assert_eq!(note.severity, Severity::Info);
            assert_eq!(note.help, "Static output never runs callbacks.");
        }
        assert_eq!(&source[found[0].span.start..found[0].span.end], "handler");
        assert!(notes(document.diagnostics(), "interaction/unsafe-url").is_empty());
        assert!(!document.has_errors(), "{:?}", document.diagnostics());
        assert!(!render_svg(&document, &SvgOptions::default())?.contains("<a "));
        Ok(())
    }

    #[test]
    fn interaction_text_output_never_carries_links() -> Result<(), RenderError> {
        let linked = with("  click A \"https://example.test\" \"tip\"\n");
        let plain = render_text(&parse(BASE), &TextOptions::default())?;
        let text = render_text(&parse(&linked), &TextOptions::default())?;
        assert_eq!(text, plain);
        assert!(!text.contains("example.test"));
        Ok(())
    }
}
