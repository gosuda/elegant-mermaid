use super::linear;
use crate::cells::Charset;
use crate::math::syntax::parse;

fn forms(source: &str, unicode: &str, ascii: &str) {
    let parsed = parse(source);
    assert_eq!(
        linear(&parsed.expression, Charset::Unicode),
        unicode,
        "unicode linear form of {source:?}"
    );
    assert_eq!(
        linear(&parsed.expression, Charset::Ascii),
        ascii,
        "ascii linear form of {source:?}"
    );
}

#[test]
fn construct_table_forms() {
    forms("x", "x", "x");
    forms("{xy}", "xy", "xy");
    forms("a,b", "a,b", "a,b");
    forms("\\frac{a}{b}", "(a)/(b)", "(a)/(b)");
    forms("\\sqrt{x}", "\u{221A}(x)", "sqrt(x)");
    forms("\\sqrt[3]{x}", "\u{00B3}\u{221A}(x)", "[3]sqrt(x)");
    forms(
        "\\sum^{n}_{k}x",
        "\u{2211}\u{207F}\u{2096}x",
        "sum^(n)_(k)x",
    );
    forms("\\prod", "\u{220F}", "prod");
    forms("\\int", "\u{222B}", "int");
    forms("\\lim", "lim", "lim");
    forms("\\lim_{x\\to 0}", "lim_(x\u{2192}0)", "lim_(x->0)");
    forms("\\infty", "\u{221E}", "inf");
    forms("\\alpha", "\u{03B1}", "alpha");
    forms("\\Gamma", "\u{0393}", "Gamma");
    forms(
        "\\pm\\times\\div\\cdot",
        "\u{00B1}\u{00D7}\u{00F7}\u{22C5}",
        "+-x/.",
    );
    forms("=", "=", "=");
    forms(
        "\\le\\ge\\ne\\approx\\to\\leftarrow\\Rightarrow\\Leftrightarrow",
        "\u{2264}\u{2265}\u{2260}\u{2248}\u{2192}\u{2190}\u{21D2}\u{21D4}",
        "<=>=!=~=-><-=><=>",
    );
    forms("\\left(x\\right)", "(x)", "(x)");
    forms("\\left|x\\right|", "|x|", "|x|");
    forms("\\left\\{x\\right\\}", "{x}", "{x}");
    forms("\\left.x\\right.", "x", "x");
    forms("\\mathbf{x}\\mathit{y}\\mathrm{z}\\text{w}", "xyzw", "xyzw");
    forms("a\\,b", "ab", "ab");
    forms("a\\;b", "a b", "a b");
    forms("a\\quad b", "a  b", "a  b");
}

#[test]
fn scripts_convert_in_unicode_and_stay_bracketed_in_ascii() {
    forms("x^{12}", "x\u{00B9}\u{00B2}", "x^(12)");
    forms("x_n", "x\u{2099}", "x_(n)");
    forms("\\sqrt[2]{x}", "\u{00B2}\u{221A}(x)", "[2]sqrt(x)");
}

#[test]
fn mixed_scripts_stay_wholly_parenthesised() {
    forms("x^{min}", "x^(min)", "x^(min)");
    forms("x_{ba}", "x_(ba)", "x_(ba)");
    forms("x^{min}_{a}", "x^(min)\u{2090}", "x^(min)_(a)");
    forms("x^{2}_{ba}", "x\u{00B2}_(ba)", "x^(2)_(ba)");
}

#[test]
fn empty_script_converts_to_nothing() {
    forms("x^{}", "x", "x^()");
    forms("x^{}_{a}", "x\u{2090}", "x^()_(a)");
}

#[test]
fn nested_constructs_keep_their_delimiters() {
    forms(
        "\\frac{\\sqrt{x}}{a+b}",
        "(\u{221A}(x))/(a+b)",
        "(sqrt(x))/(a+b)",
    );
    forms("\\sqrt{\\frac{a}{b}}", "\u{221A}((a)/(b))", "sqrt((a)/(b))");
    forms(
        "\\sqrt[\\frac{1}{2}]{x}",
        "[(1)/(2)]\u{221A}(x)",
        "[(1)/(2)]sqrt(x)",
    );
}

#[test]
fn failed_formula_prints_the_exact_source() {
    let truncated = parse("x^{");
    assert_eq!(
        truncated.diagnostics.len(),
        1,
        "truncated formula must fail: {:?}",
        truncated.diagnostics
    );
    assert_eq!(linear(&truncated.expression, Charset::Unicode), "x^{");
    assert_eq!(linear(&truncated.expression, Charset::Ascii), "x^{");
    let unsupported = parse("a\\foo{b}");
    assert_eq!(
        unsupported.diagnostics.len(),
        1,
        "unsupported command must fail: {:?}",
        unsupported.diagnostics
    );
    assert_eq!(linear(&unsupported.expression, Charset::Ascii), "a\\foo{b}");
}

#[test]
fn cdot_stays_logical_in_the_unicode_cell() {
    let parsed = parse("a\\cdot b");
    assert!(
        parsed.diagnostics.is_empty(),
        "cdot must parse: {:?}",
        parsed.diagnostics
    );
    let unicode = linear(&parsed.expression, Charset::Unicode);
    assert_eq!(unicode, "a\u{22C5}b");
    assert!(
        !unicode.contains('\u{00B7}'),
        "vector substitution U+00B7 must not reach the unicode cell"
    );
    assert_eq!(linear(&parsed.expression, Charset::Ascii), "a.b");
}
