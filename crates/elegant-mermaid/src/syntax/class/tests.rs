use super::{ast::Statement, parse};

#[test]
fn class_statement_forms() {
    let source = "classDiagram\nclass Account {\n+name\n+save() bool\n}\nAccount --> User : owns\nnote for Account \"stored\"\nnamespace Domain {\nclass User\n}\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.document.statements.len(), 4);
    let (model, diagnostics) = crate::model::class::resolve(source, &parsed.document);
    assert!(diagnostics.is_empty());
    assert_eq!(model.classes[0].attributes[0].text, "+name");
    assert_eq!(model.classes[0].methods[0].text, "+save() : bool");
    assert_eq!(model.classes[1].parent, "Domain");
    assert_eq!(model.relations[0].label, "owns");
}

#[test]
fn class_declaration_spans() {
    let source = "classDiagram\nclass A[\"Alpha\"]\n";
    let parsed = parse(source, &[]);
    assert!(matches!(
        &parsed.document.statements[0],
        Statement::Class(_)
    ));
    let Statement::Class(class) = &parsed.document.statements[0] else {
        return;
    };
    assert_eq!(
        &source[class.span.start..class.span.end],
        "class A[\"Alpha\"]"
    );
    assert_eq!(&source[class.name.span.start..class.name.span.end], "A");
}

#[test]
fn class_diagnostics() {
    for (source, code) in [
        ("classDiagram\n;\n", "class/unknown-statement"),
        ("classDiagram\nA -> B\n", "class/unexpected-token"),
        ("classDiagram\nclass A {\n", "class/unterminated"),
        (
            "classDiagram\nclass A {\n{\n}\n",
            "class/nested-member-block",
        ),
        (
            "classDiagram\n<<interface>> Missing\n",
            "class/annotation-target-unknown",
        ),
    ] {
        let parsed = parse(source, &[]);
        let (_, mut diagnostics) = crate::model::class::resolve(source, &parsed.document);
        diagnostics.extend(parsed.diagnostics);
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic.code == code),
            "{source}: {diagnostics:?}"
        );
        for diagnostic in diagnostics {
            assert!(
                diagnostic.span.start <= diagnostic.span.end && diagnostic.span.end <= source.len()
            );
        }
    }
}

#[test]
fn class_bare_names_do_not_declare() {
    let source = "classDiagram\nA\ntitle Example\nclass Service as ServiceInterface\n";
    let parsed = parse(source, &[]);
    let (model, _) = crate::model::class::resolve(source, &parsed.document);
    assert_eq!(model.classes.len(), 1);
    assert_eq!(model.classes[0].id, "ServiceasServiceInterface");
}

#[test]
fn class_metadata_generics_and_interfaces() {
    let source = "classDiagram-v2\ndirection LR\nclass A~T~:::hot {\n<<interface>>\n+find( key )$ Result~T~\n}\n<<service>> A\nA \"1\" o-- \"many\" B : stores\nA --() External\nstyle A fill:red\nclassDef hot color:blue\ncssClass \"A,B\" hot\nlink A \"https://example.test\" \"docs\" _self\naccTitle: Catalogue\naccDescr {\nA description\n}\n";
    let parsed = parse(source, &[]);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (model, diagnostics) = crate::model::class::resolve(source, &parsed.document);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    assert_eq!(model.direction, "LR");
    assert_eq!(model.classes[0].generic, "T");
    assert_eq!(model.classes[0].methods[0].text, "+find(key) : Result<T>");
    assert!(model.classes[0].methods[0].is_static);
    assert_eq!(model.relations[0].marker_start, "aggregation");
    assert_eq!(model.relations[0].multiplicity_end.as_deref(), Some("many"));
    assert_eq!(model.relations[1].to, "interface0");
    assert_eq!(model.acc_descr, "A description");
}

#[test]
fn class_rejects_namespace_relations_and_unclosed_delimiters() {
    let parsed = parse("classDiagram\nnamespace N {\nA -- B\n}\n", &[]);
    assert!(
        parsed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "class/unexpected-token")
    );
    for source in [
        "classDiagram\nclass `A",
        "classDiagram\nclass A~T",
        "classDiagram\nnote \"body",
    ] {
        let parsed = parse(source, &[]);
        assert_eq!(parsed.diagnostics[0].code, "class/unterminated");
        assert_eq!(parsed.diagnostics[0].span.end, source.len());
    }
}

#[test]
fn rejected_class_name_recovers_once() {
    let parsed = parse("classDiagram\nclass \"quoted\"\nclass Next\n", &[]);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(
        parsed.diagnostics[0].message,
        "unexpected \"quoted\", expected one of: ALPHA, BQUOTE_STR, MINUS, NUM, UNICODE_TEXT"
    );
}
