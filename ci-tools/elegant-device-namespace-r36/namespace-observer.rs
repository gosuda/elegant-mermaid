
#[cfg(all(test, windows))]
mod namespace_observer_r36 {
    use std::fmt::Write;
    use std::os::windows::ffi::OsStrExt;
    use std::path::Path;

    fn hex(value: &std::ffi::OsStr) -> String {
        let mut output = String::new();
        for unit in value.encode_wide() {
            write!(output, "{unit:04x}").expect("writing to String cannot fail");
        }
        output
    }

    #[test]
    fn raw_namespace_paths() {
        let source = std::fs::read_to_string(
            std::env::var_os("EMD_NAMESPACE_CASES").expect("frozen case file"),
        )
        .expect("read frozen UTF-8 cases");
        let mut count = 0;
        for line in source.lines() {
            let (id, input) = line.split_once('\t').expect("case ID and exact operand");
            let path = Path::new(input);
            match super::resolved_directory(path) {
                Ok(resolved) => println!(
                    "RUST_NAMESPACE\t{id}\t{}\tok\t{}\t0",
                    hex(path.as_os_str()),
                    hex(resolved.as_os_str()),
                ),
                Err(error) => println!(
                    "RUST_NAMESPACE\t{id}\t{}\terr\t{:?}\t{}",
                    hex(path.as_os_str()),
                    error.kind(),
                    error.raw_os_error().unwrap_or(-1),
                ),
            }
            count += 1;
        }
        assert_eq!(count, 12);
    }
}
