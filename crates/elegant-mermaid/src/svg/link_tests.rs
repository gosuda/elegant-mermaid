#![expect(clippy::unwrap_used, reason = "fixed link fixtures must render")]

use super::*;
use crate::{
    geom::Size,
    interaction::{OwnerLink, SafeUrl},
};

fn scene() -> Scene {
    let label = |owner, text| {
        Group::new(GroupRole::Node, owner).with_items(vec![Item::Text(TextItem {
            rect: Rect {
                x: 64,
                y: 64,
                w: 640,
                h: 1280,
            },
            role: TextRole::Label,
            size: 14,
            align: Align::Middle,
            style: TextStyle::Text,
            series: 0,
            lines: vec![vec![Run::plain(text)]],
        })])
    };
    Scene::new(
        Size { w: 1280, h: 2560 },
        Dump::new("state", DumpOptions::default()),
        vec![
            Group::new(GroupRole::Decor, ""),
            label("A", "B"),
            label("B", "A"),
            Group::new(GroupRole::Edge, "edge0"),
        ],
    )
}

fn render(links: &[OwnerLink<'_>]) -> String {
    let mut out = String::new();
    write(
        &mut out,
        &scene(),
        &Options {
            links,
            kind: "state",
            ..Options::default()
        },
    )
    .unwrap();
    out
}

#[test]
fn svg_links_wrap_matching_owner_and_escape_url_and_tooltip() {
    let links = [OwnerLink {
        owner: "A",
        url: SafeUrl::new(" \tHTTPS://example.test/?a='\"<&> \n").unwrap(),
        tooltip: Some("Open 'A' \"now\" <&>"),
    }];
    let out = render(&links);
    let opening = "<a href='HTTPS://example.test/?a=&apos;&quot;&lt;&amp;&gt;'>\n<title>Open &apos;A&apos; &quot;now&quot; &lt;&amp;&gt;</title>\n";
    assert!(
        out.contains(&format!("{opening}<g class='emd-node' id='g1'>\n")),
        "owner A, not the label A, must receive the escaped anchor"
    );
    assert_eq!(out.matches("<a ").count(), 1, "only owner A is linked");
    assert!(
        out.contains("</g>\n</a>\n<g class='emd-node' id='g2'>"),
        "owner B must remain outside the anchor"
    );
    assert!(
        out.contains("<g class='emd-decor' id='g0'>\n</g>\n<a "),
        "unrelated decoration must remain outside the anchor"
    );
    assert_eq!(
        out.replace(opening, "").replace("</a>\n", ""),
        render(&[]),
        "links must not alter labels, geometry, accessibility, or group order"
    );
}

#[test]
fn svg_links_duplicate_owner_uses_last_record_and_ignores_absent_owners() {
    let links = [
        OwnerLink {
            owner: "edge0",
            url: SafeUrl::new("http://first.test").unwrap(),
            tooltip: Some("old"),
        },
        OwnerLink {
            owner: "absent",
            url: SafeUrl::new("https://absent.test").unwrap(),
            tooltip: None,
        },
        OwnerLink {
            owner: "edge0",
            url: SafeUrl::new("mailto:last@example.test").unwrap(),
            tooltip: None,
        },
    ];
    let out = render(&links);
    let opening = "<a href='mailto:last@example.test'>\n";
    assert!(
        out.contains(&format!(
            "{opening}<g class='emd-edge' id='g3'>\n</g>\n</a>"
        )),
        "last declared edge link must wrap the matching edge group"
    );
    assert_eq!(
        out.matches("<a ").count(),
        1,
        "an absent owner must not emit an anchor"
    );
    assert!(
        !out.contains("first.test")
            && !out.contains("absent.test")
            && !out.contains("<title>old</title>"),
        "superseded and unmatched records must not leak into output"
    );
    assert_eq!(
        out.replace(opening, "").replace("</a>\n", ""),
        render(&[]),
        "a tooltip-free link must leave all other output unchanged"
    );
}
