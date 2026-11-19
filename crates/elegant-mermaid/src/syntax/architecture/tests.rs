use super::ast::{Architecture, StatementKind};
use super::lexer::lex;
use super::parse;
use crate::diag::Diagnostic;
use crate::source::Span;

fn parsed(src: &str) -> (Architecture, Vec<Diagnostic>) {
    let result = parse(src, &[]);
    (result.document, result.diagnostics)
}

fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

fn kinds(src: &str) -> Vec<&'static str> {
    lex(src, &[]).iter().map(|t| t.kind).collect()
}

#[test]
fn header_forms() {
    for header in ["architecture-beta", "architecture"] {
        let (root, diagnostics) = parsed(&format!("{header}\nservice a(server)\n"));
        assert!(diagnostics.is_empty(), "{header}");
        assert_eq!(root.header.kind, header);
        assert_eq!(root.statements.len(), 1);
    }
    let (root, diagnostics) = parsed("architecture-beta service a(server)\n");
    assert!(diagnostics.is_empty());
    assert_eq!(root.statements.len(), 1);
}

#[test]
fn statement_forms() {
    let src = "architecture-beta\n\
group g(cloud)[ \"Quoted \\\"title\\\"\" ] in p\n\
service s \"text\" [T] in g\n\
service i(logos:aws-lambda)\n\
junction j in g\n\
s{group}:R <-[ a b ]-> L:j{group}\n\
i:B -- T:s\n\
align row s i j\n";
    let (root, diagnostics) = parsed(src);
    assert!(diagnostics.is_empty());
    assert_eq!(root.statements.len(), 7);

    assert_group_statement(src, &root.statements[0]);
    assert_service_statement(&root.statements[1].kind);
    assert_icon_statement(&root.statements[2].kind);
    assert_junction_statement(&root.statements[3].kind);
    assert_labelled_edge(&root.statements[4].kind);
    assert_plain_edge(&root.statements[5].kind);
    assert_alignment_statement(src, &root.statements[6]);
}

fn assert_group_statement(src: &str, statement: &super::ast::Statement) {
    let StatementKind::Group(group) = &statement.kind else {
        assert!(matches!(statement.kind, StatementKind::Group(_)), "group");
        return;
    };
    assert_eq!(group.id.text, "g");
    assert_eq!(group.icon.as_ref().map(|v| v.text.as_str()), Some("cloud"));
    assert_eq!(
        group.title.as_ref().map(|v| v.text.as_str()),
        Some("Quoted \"title\"")
    );
    assert_eq!(group.parent.as_ref().map(|v| v.text.as_str()), Some("p"));
    let span = statement.span;
    assert_eq!(
        &src[span.start..span.end],
        "group g(cloud)[ \"Quoted \\\"title\\\"\" ] in p"
    );
}

fn assert_service_statement(kind: &StatementKind) {
    let StatementKind::Service(service) = kind else {
        assert!(matches!(kind, StatementKind::Service(_)), "service");
        return;
    };
    assert_eq!(
        service.icon_text.as_ref().map(|v| v.text.as_str()),
        Some("text")
    );
    assert!(service.icon.is_none());
    assert_eq!(service.title.as_ref().map(|v| v.text.as_str()), Some("T"));
    assert_eq!(service.parent.as_ref().map(|v| v.text.as_str()), Some("g"));
}

fn assert_icon_statement(kind: &StatementKind) {
    let StatementKind::Service(icon) = kind else {
        assert!(matches!(kind, StatementKind::Service(_)), "icon service");
        return;
    };
    assert_eq!(
        icon.icon.as_ref().map(|v| v.text.as_str()),
        Some("logos:aws-lambda")
    );
    assert!(icon.title.is_none());
}

fn assert_junction_statement(kind: &StatementKind) {
    let StatementKind::Junction(junction) = kind else {
        assert!(matches!(kind, StatementKind::Junction(_)), "junction");
        return;
    };
    assert_eq!(junction.parent.as_ref().map(|v| v.text.as_str()), Some("g"));
}

fn assert_labelled_edge(kind: &StatementKind) {
    let StatementKind::Edge(edge) = kind else {
        assert!(matches!(kind, StatementKind::Edge(_)), "edge");
        return;
    };
    assert_eq!(edge.lhs_id.text, "s");
    assert!(edge.lhs_group.is_some() && edge.lhs_into.is_some());
    assert!(edge.rhs_into.is_some() && edge.rhs_group.is_some());
    assert_eq!(edge.title.as_ref().map(|v| v.text.as_str()), Some("a b"));
    assert_eq!(
        (edge.lhs_dir.text.as_str(), edge.rhs_dir.text.as_str()),
        ("R", "L")
    );
    assert_eq!(edge.rhs_id.text, "j");
}

fn assert_plain_edge(kind: &StatementKind) {
    let StatementKind::Edge(plain) = kind else {
        assert!(matches!(kind, StatementKind::Edge(_)), "plain edge");
        return;
    };
    assert!(plain.lhs_group.is_none() && plain.title.is_none() && plain.lhs_into.is_none());
}

fn assert_alignment_statement(src: &str, statement: &super::ast::Statement) {
    let StatementKind::Alignment(align) = &statement.kind else {
        assert!(
            matches!(statement.kind, StatementKind::Alignment(_)),
            "alignment"
        );
        return;
    };
    assert_eq!(align.direction.text, "row");
    assert_eq!(align.members.len(), 3);
    assert_eq!(
        statement.span,
        Span {
            start: statement.span.start,
            end: src.len() - 1
        }
    );
}

#[test]
fn metadata_statements_merge() {
    let (root, diagnostics) = parsed(
        "architecture-beta\ntitle  A   B\naccTitle: t %% c\naccDescr {\n a  b\n\n c\n}\nservice a(server)\ntitle second\n",
    );
    assert!(diagnostics.is_empty());
    assert_eq!(root.statements.len(), 3);
    let StatementKind::Metadata(meta) = &root.statements[0].kind else {
        assert!(
            matches!(root.statements[0].kind, StatementKind::Metadata(_)),
            "metadata"
        );
        return;
    };
    assert_eq!(meta.items.len(), 3);
    assert_eq!(
        (meta.items[0].field, meta.items[0].value.as_str()),
        ("title", "A B")
    );
    assert_eq!(meta.items[1].value, "t");
    assert_eq!(meta.items[2].value, "a b\nc");
}

#[test]
fn port_letters_win_over_identifiers() {
    assert_eq!(
        kinds("architecture-beta\nservice Lambda"),
        [
            "architecture-beta",
            "NEWLINE",
            "service",
            "ARROW_DIRECTION",
            "ID",
            "EOF"
        ]
    );
    for src in [
        "left_disk",
        "1Leftofmid",
        "trueblue",
        "group-1",
        "accTitle1",
    ] {
        assert_eq!(kinds(src), ["ID", "EOF"], "{src}");
    }
    assert_eq!(kinds("group-"), ["group", "-", "EOF"]);
    assert_eq!(kinds("title1"), ["TITLE", "ID", "EOF"]);
}

#[test]
fn arrow_tokens() {
    assert_eq!(
        kinds("a:R<-->L:b{group}"),
        [
            "ID",
            ":",
            "ARROW_DIRECTION",
            "ARROW_INTO",
            "--",
            "ARROW_INTO",
            "ARROW_DIRECTION",
            ":",
            "ID",
            "ARROW_GROUP",
            "EOF"
        ]
    );
    assert_eq!(kinds("-[x]-"), ["-", "ARCH_TITLE", "-", "EOF"]);
}

#[test]
fn title_and_icon_values() {
    for (input, kind, text) in [
        ("[ x ]", "ARCH_TITLE", "x"),
        ("[\"x y\"]", "ARCH_TITLE", "x y"),
        ("['it\\'s']", "ARCH_TITLE", "it's"),
        ("[\"x]", "ARCH_TITLE", "\"x"),
        ("[\"a\"b]", "ARCH_TITLE", "\"a\"b"),
        ("[\" \"]", "ARCH_TITLE", ""),
        ("(a-b:c)", "ARCH_ICON", "a-b:c"),
        ("\"a\\nb\"", "STRING", "a\nb"),
        ("'q\\'q'", "STRING", "q'q"),
    ] {
        let tokens = lex(input, &[]);
        assert_eq!(tokens[0].kind, kind, "{input}");
        assert_eq!(tokens[0].text, text, "{input}");
        assert_eq!(
            tokens[0].span,
            Span {
                start: 0,
                end: input.len()
            },
            "{input}"
        );
    }
}

#[test]
fn unterminated_and_invalid_delimiters() {
    for (src, token) in [
        ("architecture-beta\nservice a(server", "("),
        ("architecture-beta\nservice a[title", "["),
        ("architecture-beta\nservice a \"text", "\""),
        ("architecture-beta\naccDescr {\nnever", "{"),
    ] {
        let (_, diagnostics) = parsed(src);
        assert_eq!(
            messages(&diagnostics),
            [format!("architecture/unterminated: unterminated {token}")],
            "{src}"
        );
        assert_eq!(diagnostics[0].span.end, src.len(), "{src}");
    }
    for src in [
        "service a(a b)",
        "service a()",
        "service a[]",
        "service a[x\ny]",
        "service a[x[y]]",
        "service a;",
        "service \"a\\\n\"",
    ] {
        let (_, diagnostics) = parsed(&format!("architecture-beta\n{src}\n"));
        assert!(!diagnostics.is_empty(), "{src}");
    }
}

fn marked(src: &str) -> Result<(String, Span), &'static str> {
    let start = src.find('|').ok_or("missing opening span marker")?;
    let last = src.rfind('|').ok_or("missing closing span marker")?;
    if start == last {
        return Err("missing closing span marker");
    }
    let end = last - 1;
    let clean = format!(
        "{}{}{}",
        &src[..start],
        &src[start + 1..=end],
        &src[end + 2..]
    );
    Ok((clean, Span { start, end }))
}

#[test]
fn diagnostics() -> Result<(), &'static str> {
    for (src, want) in [
        (
            "architecture-beta\nfoo |bar|\n",
            "architecture/unexpected-token: unexpected bar, expected one of: :, ARROW_GROUP",
        ),
        (
            "architecture-beta\n|-- x|\n",
            "architecture/unknown-statement: unknown statement --",
        ),
        (
            "architecture-beta\nservice |L|\n",
            "architecture/unexpected-token: unexpected L, expected one of: ID",
        ),
        (
            "architecture-beta\nservice a[x]|(y)|\n",
            "architecture/unexpected-token: unexpected (y), expected one of: EOF, NEWLINE, in",
        ),
        (
            "architecture-beta\nservice a (x) |(y)|\n",
            "architecture/unexpected-token: unexpected (y), expected one of: ARCH_TITLE, EOF, NEWLINE, in",
        ),
        (
            "architecture-beta\njunction j|[T]|\n",
            "architecture/unexpected-token: unexpected [T], expected one of: EOF, NEWLINE, in",
        ),
        (
            "architecture-beta\na:|X| -- L:b\n",
            "architecture/invalid-direction: invalid edge direction X; expected L, R, T, B",
        ),
        (
            "architecture-beta\na:R -- |l|:b\n",
            "architecture/invalid-direction: invalid edge direction l; expected L, R, T, B",
        ),
        (
            "architecture-beta\na:R --|-| L:b\n",
            "architecture/unexpected-token: unexpected -, expected one of: ARROW_DIRECTION, ARROW_INTO",
        ),
        (
            "architecture-beta\na:R <- |L|:b\n",
            "architecture/unexpected-token: unexpected L, expected one of: ARCH_TITLE",
        ),
        (
            "architecture-beta\n|align row a|\n",
            "architecture/align-too-few-members: alignment requires at least two members",
        ),
        (
            "architecture-beta\nalign |diag| a b\n",
            "architecture/unexpected-token: unexpected diag, expected one of: column, row",
        ),
        (
            "architecture-beta\nalign row a b |:|\n",
            "architecture/unexpected-token: unexpected :, expected one of: EOF, ID, NEWLINE",
        ),
        (
            "architecture-beta\nservice a(server) |service| b(server)\n",
            "architecture/unexpected-token: unexpected service, expected one of: ARCH_TITLE, EOF, NEWLINE, in",
        ),
    ] {
        let (clean, span) = marked(src)?;
        let (_, diagnostics) = parsed(&clean);
        assert_eq!(messages(&diagnostics), [want], "{clean}");
        assert_eq!(diagnostics[0].span, span, "{clean}");
    }
    Ok(())
}

#[test]
fn recovery_continues_on_the_next_line() {
    let (root, diagnostics) =
        parsed("architecture-beta\nservice a(server)\nservice (x)\nservice b(server)\n");
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(root.statements.len(), 2);
}
