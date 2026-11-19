use super::{Metric, Role, segment};
use crate::geom::GeomError;

#[test]
fn measure_vector_parity_values() -> Result<(), GeomError> {
    for (text, width) in [("Start", 2086), ("Choice", 3041), ("yes", 1550)] {
        assert_eq!(Metric::for_role(Role::Label).width(text)?, width);
    }
    assert_eq!(
        segment("🇦🇧🇨🇩🇪").iter().map(|c| c.text).collect::<Vec<_>>(),
        vec!["🇦🇧", "🇨🇩", "🇪"]
    );
    Ok(())
}
#[test]
fn measure_unicode_grapheme_break_test() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../spec/data/unicode/GraphemeBreakTest.txt");
    if !path.exists() {
        return Ok(());
    }
    let contents = std::fs::read_to_string(path)?;
    for (line_number, line) in contents.lines().enumerate() {
        let data = line.split('#').next().unwrap_or("").trim();
        if data.is_empty() {
            continue;
        }
        check_line(data, line_number)?;
    }
    Ok(())
}
fn check_line(data: &str, line_number: usize) -> Result<(), Box<dyn std::error::Error>> {
    let mut text = String::new();
    let mut boundaries = Vec::new();
    for token in data.split_whitespace() {
        match token {
            "÷" => boundaries.push(text.len()),
            "×" => (),
            _ => {
                text.push(char::from_u32(u32::from_str_radix(token, 16)?).ok_or("invalid scalar")?)
            }
        }
    }
    let mut actual = vec![0];
    let mut offset = 0;
    for cluster in segment(&text) {
        offset += cluster.text.len();
        actual.push(offset);
    }
    assert_eq!(
        actual,
        boundaries,
        "GraphemeBreakTest line {}",
        line_number + 1
    );
    Ok(())
}
