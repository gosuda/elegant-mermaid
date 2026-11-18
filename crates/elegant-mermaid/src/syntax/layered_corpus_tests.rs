const SCRIPT: &str = "import json,sys\nv=json.load(open('corpus/verdicts.json'))\nd={r['path'] for r in json.load(open('corpus/divergences.json'))}\nfor p,r in v.items():\n if p.startswith('corpus/'+sys.argv[1]+'/') and p not in d: print(str(int(r['accept']))+' '+p)";

fn verdicts(kind: &str) -> std::io::Result<()> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let result = std::process::Command::new("python3")
        .arg("-c")
        .arg(SCRIPT)
        .arg(kind)
        .current_dir(&root)
        .output()?;
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let mut mismatches = Vec::new();
    let mut count = 0;
    for line in String::from_utf8_lossy(&result.stdout).lines() {
        let Some((accept, path)) = line.split_once(' ') else {
            continue;
        };
        let source = match std::fs::read_to_string(root.join(path)) {
            Ok(source) => source,
            Err(error) => {
                mismatches.push(format!("{path}: {error}"));
                continue;
            }
        };
        count += 1;
        let document = crate::parse(&source);
        if !document.has_errors() != (accept == "1") {
            mismatches.push(format!(
                "{path}: expected {accept}, diagnostics {:?}",
                document.diagnostics()
            ));
        }
    }
    assert!(count > 0, "{kind} corpus was empty");
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
    Ok(())
}

#[test]
fn c4_corpus_verdicts() -> std::io::Result<()> {
    verdicts("c4")
}

#[test]
fn requirement_corpus_verdicts() -> std::io::Result<()> {
    verdicts("requirement")
}

#[test]
fn er_corpus_verdicts() -> std::io::Result<()> {
    verdicts("er")
}

#[test]
fn agentflow_corpus_verdicts() -> std::io::Result<()> {
    verdicts("agentflow")
}

#[test]
fn usecase_corpus_verdicts() -> std::io::Result<()> {
    verdicts("usecase")
}

#[test]
fn railroad_corpus_verdicts() -> std::io::Result<()> {
    verdicts("railroad")
}
