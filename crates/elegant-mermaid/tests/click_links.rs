use elegant_mermaid::{RenderError, SvgOptions, parse, render_svg};

fn svg(source: &str) -> Result<String, RenderError> {
    let document = parse(source);
    assert!(
        !document.has_errors(),
        "{source:?}: {:?}",
        document.diagnostics()
    );
    render_svg(&document, &SvgOptions::default())
}

fn first_anchor(svg: &str) -> &str {
    let after = svg.split("<a ").nth(1).unwrap_or_default();
    after.split("</a>").next().unwrap_or_default()
}

#[test]
fn state_click_links_wrap_their_simple_state_only() -> Result<(), RenderError> {
    let out = svg(
        "stateDiagram-v2\n  A --> B\n  click A \"https://example.test/a?x=1&y=2\" \"Open <a>\"\n  click B href \"javascript:alert(1)\"\n  state C {\n    D --> E\n  }\n  click C href \"https://example.test/c\"\n  click E href \"https://example.test/e\"\n  click D \"https://example.test/d\" \"\"\n",
    )?;
    assert_eq!(out.matches("<a ").count(), 3, "{out}");
    assert!(
        !out.contains("javascript")
            && !out.contains("example.test/c")
            && !out.contains("<title></title>"),
        "unsafe URL, composite state, or empty tooltip reached the SVG: {out}"
    );
    let block = first_anchor(&out);
    assert!(
        block.starts_with(
            "href='https://example.test/a?x=1&amp;y=2'>\n<title>Open &lt;a&gt;</title>\n<g class='emd-node' "
        ),
        "{block}"
    );
    assert!(
        block.contains(">A</tspan>") && !block.contains(">B</tspan>"),
        "{block}"
    );
    Ok(())
}

#[test]
fn flowchart_click_with_an_empty_tooltip_emits_no_title() -> Result<(), RenderError> {
    let out = svg("flowchart LR\n  A --> B\n  click A \"https://example.test/a\" \"\"\n")?;
    assert_eq!(out.matches("<a ").count(), 1, "{out}");
    assert!(!out.contains("<title></title>"), "{out}");
    Ok(())
}

#[test]
fn agentflow_click_links_wrap_their_node() -> Result<(), RenderError> {
    let out = svg(
        "agentflow-beta\n  A --> B\n  click A \"https://example.test/a?x=1&y=2\" \"Open <a>\"\n  click B \"javascript:alert(1)\"\n",
    )?;
    assert_eq!(out.matches("<a ").count(), 1, "{out}");
    assert!(!out.contains("javascript"), "{out}");
    let block = first_anchor(&out);
    assert!(
        block.starts_with(
            "href='https://example.test/a?x=1&amp;y=2'>\n<title>Open &lt;a&gt;</title>\n<g class='emd-node' "
        ),
        "{block}"
    );
    assert!(
        block.contains(">A</tspan>") && !block.contains(">B</tspan>"),
        "{block}"
    );
    Ok(())
}

#[test]
fn flowchart_click_on_a_subgraph_draws_no_anchor() -> Result<(), RenderError> {
    let out = svg(
        "flowchart LR\n  subgraph S\n    C\n  end\n  click S \"https://example.test/s\"\n  click C \"https://example.test/c\"\n",
    )?;
    assert_eq!(out.matches("<a ").count(), 1, "{out}");
    assert!(!out.contains("example.test/s"), "{out}");
    assert!(first_anchor(&out).contains(">C</tspan>"), "{out}");
    Ok(())
}
