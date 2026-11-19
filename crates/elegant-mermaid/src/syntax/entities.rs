//! Entity decoding of label text (`spec/preprocessing.md`): `#N;` gives the scalar `N`, and
//! `#name;` gives the WHATWG named character reference; any other form stays literal.

pub(crate) fn decode_entities(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find('#') {
        out.push_str(rest.get(..at).unwrap_or(""));
        let tail = rest.get(at + 1..).unwrap_or("");
        match entity(tail) {
            Some((length, value)) => {
                out.push_str(&value);
                rest = tail.get(length..).unwrap_or("");
            }
            None => {
                out.push('#');
                rest = tail;
            }
        }
    }
    out.push_str(rest);
    out
}

fn entity(tail: &str) -> Option<(usize, String)> {
    let end = tail
        .bytes()
        .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        .count();
    if end == 0 || tail.as_bytes().get(end) != Some(&b';') {
        return None;
    }
    entity_value(tail.get(..end)?).map(|value| (end + 1, value))
}

fn entity_value(name: &str) -> Option<String> {
    if let Ok(number) = name.parse::<u32>() {
        return char::from_u32(number)
            .filter(|character| *character != '\0')
            .map(String::from);
    }
    let key = format!("&{name};");
    let table = crate::r#gen::entities::ENTITIES;
    let at = table
        .binary_search_by(|row| row.name.cmp(key.as_str()))
        .ok()?;
    Some(
        table
            .get(at)?
            .cps
            .iter()
            .copied()
            .filter_map(char::from_u32)
            .collect(),
    )
}
