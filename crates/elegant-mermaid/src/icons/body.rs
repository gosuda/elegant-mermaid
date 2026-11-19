pub(super) fn path_data(body: &str) -> Option<Vec<String>> {
    let mut rest = body.trim_matches(is_space);
    let mut out = Vec::new();
    while !rest.is_empty() {
        let after = rest.strip_prefix("<path")?;
        let (data, tail) = element(after)?;
        out.push(data);
        rest = tail.trim_start_matches(is_space);
    }
    Some(out)
}

fn is_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\r' | '\n' | '\u{c}')
}

fn element(after: &str) -> Option<(String, &str)> {
    if !after.starts_with(is_space) {
        return None;
    }
    let mut rest = after;
    let mut data = None;
    loop {
        rest = rest.trim_start_matches(is_space);
        for close in ["/>", "></path>"] {
            if let Some(tail) = rest.strip_prefix(close) {
                return Some((data?, tail));
            }
        }
        let (name, value, tail) = attribute(rest)?;
        if name == "d" {
            data = Some(value.to_owned());
        } else if name != "fill" || value != "currentColor" {
            return None;
        }
        rest = tail;
    }
}

fn attribute(text: &str) -> Option<(&str, &str, &str)> {
    let (name, rest) = text.split_once('=')?;
    let breaks_name = |c: char| is_space(c) || matches!(c, '<' | '>' | '/' | '"' | '\'');
    if name.is_empty() || name.contains(breaks_name) {
        return None;
    }
    let quote = rest.chars().next().filter(|c| matches!(c, '"' | '\''))?;
    let (value, tail) = rest[1..].split_once(quote)?;
    Some((name, value, tail))
}

#[cfg(test)]
mod tests {
    use super::path_data;

    #[test]
    fn reads_path_elements_in_order() {
        assert_eq!(
            path_data(r#"<path fill="currentColor" d="M0 0h1"/> <path d='M1 1'></path>"#),
            Some(vec!["M0 0h1".to_owned(), "M1 1".to_owned()])
        );
    }

    #[test]
    fn every_other_construct_is_unsupported() {
        for body in [
            "<circle cx='1' cy='1' r='1'/>",
            "<g><path d='M0 0'/></g>",
            "<path fill='red'/>",
            "<path d='M0 0'/>text",
            "<pathx d='M0 0'/>",
            "<path d=M0/>",
            "<path d='M0 0'",
            "<path d='M0 0'>",
            "<!-- c --><path d='M0 0'/>",
        ] {
            assert_eq!(path_data(body), None, "{body:?}");
        }
        assert_eq!(path_data(""), Some(Vec::new()));
    }
}
