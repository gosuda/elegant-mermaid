use super::*;

pub(super) fn resolve_plain(text: &str) -> ConfigValue {
    match text {
        "" | "null" | "Null" | "NULL" | "~" => ConfigValue::Null,
        "true" | "True" | "TRUE" => ConfigValue::Bool(true),
        "false" | "False" | "FALSE" => ConfigValue::Bool(false),
        _ => {
            let b = text.as_bytes();
            let ds = match b.first() {
                Some(b'+') | Some(b'-') => 1,
                _ => 0,
            };
            if all_digits(&b[ds..]) {
                return ConfigValue::Integer(text.to_string());
            }
            if decimal_shape(b) {
                return ConfigValue::Decimal(text.to_string());
            }
            ConfigValue::String(text.to_string())
        }
    }
}

pub(super) fn all_digits(b: &[u8]) -> bool {
    !b.is_empty() && b.iter().all(|c| c.is_ascii_digit())
}

pub(super) fn decimal_shape(b: &[u8]) -> bool {
    let Some(dot) = b.iter().position(|c| *c == b'.') else {
        return false;
    };
    let mut head = &b[..dot];
    if matches!(head.first(), Some(b'+') | Some(b'-')) {
        head = &head[1..];
    }
    all_digits(head) && all_digits(&b[dot + 1..])
}

pub(super) fn add_one(s: &str) -> String {
    let mut out = s.as_bytes().to_vec();
    let mut i = out.len();
    while i > 0 {
        i -= 1;
        if out[i] == b'9' {
            out[i] = b'0';
        } else {
            out[i] += 1;
            return String::from_utf8(out).unwrap_or_else(|_| s.to_string());
        }
    }
    let mut r = String::from("1");
    r.push_str(&String::from_utf8(out).unwrap_or_default());
    r
}

pub(super) fn parse_exp_clamped(digits: &str, neg: bool) -> i64 {
    let mut v = 0i64;
    for c in digits.bytes() {
        v = v.saturating_mul(10).saturating_add(i64::from(c - b'0'));
    }
    let lim = 999999999i64;
    if v > lim {
        v = lim;
    }
    if neg { -v } else { v }
}

pub(super) fn scan_sign(b: &[u8], i: &mut usize) -> bool {
    match b.first() {
        Some(b'-') => {
            *i = 1;
            true
        }
        Some(b'+') => {
            *i = 1;
            false
        }
        _ => false,
    }
}

pub(super) fn scan_digits<'a>(b: &'a [u8], i: &mut usize) -> &'a [u8] {
    let s = *i;
    while matches!(b.get(*i), Some(c) if c.is_ascii_digit()) {
        *i += 1;
    }
    &b[s..*i]
}

pub(super) fn scan_frac<'a>(b: &'a [u8], i: &mut usize) -> Option<&'a [u8]> {
    if b.get(*i) != Some(&b'.') {
        return Some(&[]);
    }
    *i += 1;
    let f = scan_digits(b, i);
    if f.is_empty() { None } else { Some(f) }
}

pub(super) fn scan_exp(b: &[u8], i: &mut usize) -> Option<i64> {
    if !matches!(b.get(*i), Some(b'e') | Some(b'E')) {
        return Some(0);
    }
    *i += 1;
    let neg = match b.get(*i) {
        Some(b'-') => {
            *i += 1;
            true
        }
        Some(b'+') => {
            *i += 1;
            false
        }
        _ => false,
    };
    let d = scan_digits(b, i);
    if d.is_empty() {
        return None;
    }
    let Ok(s) = std::str::from_utf8(d) else {
        return None;
    };
    Some(parse_exp_clamped(s, neg))
}

pub(super) fn thousandths_text(text: &str) -> Option<i32> {
    let b = text.as_bytes();
    let mut i = 0usize;
    let neg = scan_sign(b, &mut i);
    let int = scan_digits(b, &mut i);
    let frac = scan_frac(b, &mut i)?;
    let exp = scan_exp(b, &mut i)?;
    if i != b.len() {
        return None;
    }
    finish_thousandths(int, frac, exp, neg)
}

pub(super) fn finish_thousandths(
    int_digits: &[u8],
    frac_digits: &[u8],
    exp: i64,
    neg: bool,
) -> Option<i32> {
    let mut raw = Vec::with_capacity(int_digits.len() + frac_digits.len());
    raw.extend_from_slice(int_digits);
    raw.extend_from_slice(frac_digits);
    let Ok(dtext) = String::from_utf8(raw) else {
        return None;
    };
    let trimmed = dtext.trim_start_matches('0');
    let d = if trimmed.is_empty() { "0" } else { trimmed };
    let t = mantissa_thousandths(d, exp, i64::try_from(frac_digits.len()).unwrap_or(i64::MAX))?;
    let Ok(tv) = t.parse::<u64>() else {
        return None;
    };
    if tv > 2147483647 {
        return None;
    }
    let Ok(mag) = i64::try_from(tv) else {
        return None;
    };
    let signed = if neg { -mag } else { mag };
    i32::try_from(signed).ok()
}

pub(super) fn mantissa_thousandths(d: &str, exp: i64, k: i64) -> Option<String> {
    if d == "0" {
        return Some(String::from("0"));
    }
    let p = exp - k + 3;
    if p > 10 {
        return None;
    }
    if p >= 0 {
        let mut t = String::from(d);
        for _ in 0..p {
            t.push('0');
        }
        return Some(t);
    }
    let r = usize::try_from(-p).unwrap_or(usize::MAX);
    let len = d.len();
    if len < r {
        return Some(String::from("0"));
    }
    let keep = &d[..len - r];
    let mut t = if keep.is_empty() {
        String::from("0")
    } else {
        String::from(keep)
    };
    if d.as_bytes()[len - r] >= b'5' {
        t = add_one(&t);
    }
    Some(t)
}
