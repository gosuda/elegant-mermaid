//! JavaScript value semantics of kanban node metadata: truthiness and string conversion.

use crate::syntax::config_value::{ConfigValue, Entry};

const OBJECT_TEXT: &str = "[object Object]";
const MAX_FIXED_POINT: i64 = 21;
const MIN_FIXED_POINT: i64 = -6;

fn number(text: &str) -> f64 {
    text.parse::<f64>().unwrap_or(f64::NAN)
}

pub(super) fn truthy(value: &ConfigValue) -> bool {
    match value {
        ConfigValue::Null => false,
        ConfigValue::Bool(flag) => *flag,
        ConfigValue::Integer(text) | ConfigValue::Decimal(text) => {
            let parsed = number(text);
            parsed != 0.0 && !parsed.is_nan()
        }
        ConfigValue::String(text) => !text.is_empty(),
        ConfigValue::Sequence(_) | ConfigValue::Mapping(_) => true,
    }
}

pub(super) fn js_string(value: &ConfigValue) -> String {
    match value {
        ConfigValue::Null => String::new(),
        ConfigValue::Bool(flag) => flag.to_string(),
        ConfigValue::Integer(text) | ConfigValue::Decimal(text) => js_number(number(text)),
        ConfigValue::String(text) => text.clone(),
        ConfigValue::Sequence(items) => items.iter().map(js_string).collect::<Vec<_>>().join(","),
        ConfigValue::Mapping(_) => OBJECT_TEXT.to_owned(),
    }
}

pub(super) fn convertible(value: &ConfigValue) -> bool {
    match value {
        ConfigValue::Sequence(items) => items.iter().all(convertible),
        ConfigValue::Mapping(entries) => {
            !entries.iter().any(|entry: &Entry| entry.key == "toString")
        }
        _ => true,
    }
}

fn js_number(value: f64) -> String {
    if value.is_nan() {
        return "NaN".to_owned();
    }
    if value.is_infinite() {
        return if value > 0.0 { "Infinity" } else { "-Infinity" }.to_owned();
    }
    if value == 0.0 {
        return "0".to_owned();
    }
    let (sign, magnitude) = if value < 0.0 {
        ("-", -value)
    } else {
        ("", value)
    };
    let text = format!("{magnitude:e}");
    let (mantissa, exponent) = text.split_once('e').unwrap_or((text.as_str(), "0"));
    let digits: String = mantissa.chars().filter(|c| *c != '.').collect();
    let point = exponent.parse::<i64>().unwrap_or(0) + 1;
    format!("{sign}{}", layout_digits(&digits, point))
}

fn layout_digits(digits: &str, point: i64) -> String {
    let length = i64::try_from(digits.len()).unwrap_or(i64::MAX);
    if length <= point && point <= MAX_FIXED_POINT {
        let zeros = usize::try_from(point - length).unwrap_or(0);
        return format!("{digits}{}", "0".repeat(zeros));
    }
    if 0 < point && point <= MAX_FIXED_POINT {
        let split = usize::try_from(point).unwrap_or(0);
        return format!(
            "{}.{}",
            digits.get(..split).unwrap_or(""),
            digits.get(split..).unwrap_or("")
        );
    }
    if MIN_FIXED_POINT < point && point <= 0 {
        let zeros = usize::try_from(-point).unwrap_or(0);
        return format!("0.{}{digits}", "0".repeat(zeros));
    }
    let scale = point - 1;
    let (sign, scale) = if scale < 0 {
        ('-', -scale)
    } else {
        ('+', scale)
    };
    match digits.split_at_checked(1) {
        Some((head, tail)) if !tail.is_empty() => format!("{head}.{tail}e{sign}{scale}"),
        _ => format!("{digits}e{sign}{scale}"),
    }
}

#[cfg(test)]
mod tests {
    use super::{js_number, number};

    #[test]
    fn javascript_number_text() {
        for (text, want) in [
            ("0", "0"),
            ("-0", "0"),
            ("007", "7"),
            ("+5", "5"),
            ("1.50", "1.5"),
            ("0.000001", "0.000001"),
            ("0.0000001", "1e-7"),
            ("123456789012345678901", "123456789012345680000"),
            ("1234567890123456789012", "1.2345678901234568e+21"),
            ("-12.25", "-12.25"),
        ] {
            assert_eq!(js_number(number(text)), want, "{text}");
        }
        assert_eq!(js_number(number(&"9".repeat(400))), "Infinity");
    }
}
