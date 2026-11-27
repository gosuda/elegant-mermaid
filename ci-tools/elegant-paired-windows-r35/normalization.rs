use std::path::{Path, PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let base = PathBuf::from(std::env::var_os("EMD_TEST_LOCAL_ROOT").ok_or("missing native root")?)
        .join("normalization-observer");
    std::fs::create_dir(&base)?;
    std::fs::create_dir(base.join("assets"))?;
    std::fs::create_dir(base.join("assets/child"))?;
    let literal = base.canonicalize()?;
    std::fs::create_dir(literal.join("literal "))?;
    std::fs::create_dir(literal.join("literal /child"))?;
    for name in [
        "assets.", "assets ", "assets..", "assets. ", "assets...",
        r"assets.\child", r"assets \child", r"assets..\child",
        ".", "..", "...", ". ", ".. ", "... ", " ", " a", "a\t",
        r"assets.\..\future", r"literal \child",
    ] {
        let operand = base.join(name);
        println!(
            "WINDOWS_NORMALIZE name={name:?} absolute={:?} canonical={:?} isolated={:?}",
            std::path::absolute(&operand),
            operand.canonicalize(),
            std::path::absolute(Path::new(r"C:\__emd_component__").join(name))
        );
    }
    Ok(())
}
