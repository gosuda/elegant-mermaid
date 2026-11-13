//! Validated static-output links. Raw source URLs remain in the semantic model.

/// A borrowed URL with an explicitly allowed static-output scheme.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SafeUrl<'a>(&'a str);

impl<'a> SafeUrl<'a> {
    /// Trim ASCII whitespace and accept only http, https, or mailto before the first colon.
    /// Scheme comparison is ASCII case-insensitive; the returned text keeps its case.
    pub fn new(raw: &'a str) -> Option<Self> {
        let url =
            raw.trim_matches(|c: char| matches!(c, ' ' | '\t' | '\n' | '\r' | '\u{b}' | '\u{c}'));
        let (scheme, _) = url.split_once(':')?;
        if scheme.eq_ignore_ascii_case("http")
            || scheme.eq_ignore_ascii_case("https")
            || scheme.eq_ignore_ascii_case("mailto")
        {
            Some(Self(url))
        } else {
            None
        }
    }

    /// The validated URL, with surrounding ASCII whitespace removed.
    pub fn as_str(self) -> &'a str {
        self.0
    }
}

/// A static link for scene groups whose owner ID matches `owner`.
/// Repeated owner IDs in SVG options resolve to the last record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OwnerLink<'a> {
    pub owner: &'a str,
    pub url: SafeUrl<'a>,
    pub tooltip: Option<&'a str>,
}

#[cfg(test)]
mod tests {
    use super::SafeUrl;

    #[test]
    fn allowed_schemes_trim_ascii_and_preserve_borrowed_text() {
        for (raw, expected) in [
            (
                " \t\r\n\u{b}\u{c}HtTp://example.test/a \t",
                "HtTp://example.test/a",
            ),
            ("HTTPS://example.test", "HTTPS://example.test"),
            ("mAiLtO:person@example.test", "mAiLtO:person@example.test"),
            (
                "https://example.test/javascript:literal",
                "https://example.test/javascript:literal",
            ),
        ] {
            assert_eq!(
                SafeUrl::new(raw).map(SafeUrl::as_str),
                Some(expected),
                "allowed URL {raw:?}"
            );
        }
    }

    #[test]
    fn unsupported_or_misleading_schemes_are_rejected() {
        for raw in [
            "",
            "example.test",
            "/relative",
            "//example.test",
            "javascript:alert(1)",
            "data:text/plain,hello",
            "javascript:https://example.test",
            "httpsx://example.test",
            "https ://example.test",
            "ht\ttps://example.test",
            ":https://example.test",
            "\u{a0}https://example.test",
            "\u{2003}https://example.test",
            "ＨＴＴＰＳ://example.test",
        ] {
            assert_eq!(
                SafeUrl::new(raw),
                None,
                "unsafe URL {raw:?} must not become an output link"
            );
        }
    }

    #[test]
    fn trailing_non_ascii_whitespace_is_not_trimmed() {
        let raw = "https://example.test/\u{a0}";
        assert_eq!(SafeUrl::new(raw).map(SafeUrl::as_str), Some(raw));
    }
}
