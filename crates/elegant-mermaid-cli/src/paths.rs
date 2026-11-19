//! Lexical path helpers that name files the way Go's `filepath` package does,
//! so directory walks print the same paths as the Go CLI.

/// Lexical path cleaning, as Go's `filepath.Clean` does it on Unix.
pub fn clean(path: &str) -> String {
    let rooted = path.starts_with('/');
    let mut parts: Vec<&str> = Vec::new();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." if parts.last().is_some_and(|last| *last != "..") => {
                parts.pop();
            }
            ".." if rooted => {}
            other => parts.push(other),
        }
    }
    let joined = parts.join("/");
    match (rooted, joined.is_empty()) {
        (true, _) => format!("/{joined}"),
        (false, true) => ".".into(),
        (false, false) => joined,
    }
}

/// `filepath.Join` for two elements: an empty directory gives the bare name.
pub fn join(dir: &str, name: &str) -> String {
    if dir.is_empty() {
        return clean(name);
    }
    clean(&format!("{dir}/{name}"))
}

/// Everything before the last slash, cleaned, as Go's `filepath.Dir` has it.
pub fn directory(path: &str) -> String {
    match path.rfind('/') {
        Some(at) => clean(&path[..=at]),
        None => ".".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_matches_go_filepath_clean() {
        for (path, want) in [
            ("/a/b/../c/./d", "/a/c/d"),
            ("/../a", "/a"),
            ("a//b", "a/b"),
            ("../a/..", ".."),
            ("a/..", "."),
            ("./", "."),
            ("/", "/"),
            ("../../x", "../../x"),
        ] {
            assert_eq!(clean(path), want, "{path}");
        }
    }

    #[test]
    fn join_matches_go_filepath_join() {
        for (dir, name, want) in [
            (".", "a.mmd", "a.mmd"),
            ("./docs", "a.mmd", "docs/a.mmd"),
            ("docs/", "a.mmd", "docs/a.mmd"),
            ("/", "a.mmd", "/a.mmd"),
            ("", "a.mmd", "a.mmd"),
            ("../x", "a.mmd", "../x/a.mmd"),
        ] {
            assert_eq!(join(dir, name), want, "{dir} {name}");
        }
    }

    #[test]
    fn directory_matches_go_filepath_dir() {
        for (path, want) in [
            ("a.mmd", "."),
            ("-", "."),
            ("x/y.mmd", "x"),
            ("/x/y.mmd", "/x"),
            ("/y.mmd", "/"),
            ("x/", "x"),
            ("a/b/", "a/b"),
        ] {
            assert_eq!(directory(path), want, "{path}");
        }
    }
}
