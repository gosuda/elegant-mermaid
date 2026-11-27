
#[cfg(all(test, windows))]
mod review_windows_tests {
    use super::{relative_url, resolved_directory};
    use std::ffi::OsString;
    use std::io;
    use std::path::{Component, Path, PathBuf, Prefix};

    struct Directory(PathBuf);

    impl Directory {
        fn new(label: &str, network: bool) -> io::Result<Self> {
            let root = std::env::var_os(if network {
                "EMD_TEST_UNC_ROOT"
            } else {
                "EMD_TEST_LOCAL_ROOT"
            })
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "native test root missing"))?;
            let path = PathBuf::from(root).join(label);
            std::fs::create_dir(&path)?;
            Ok(Self(path.canonicalize()?))
        }

        fn ordinary(&self) -> PathBuf {
            ordinary(&self.0)
        }
    }

    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn ordinary(path: &Path) -> PathBuf {
        let mut parts = path.components();
        let mut out = match parts.next() {
            Some(Component::Prefix(prefix)) => match prefix.kind() {
                Prefix::VerbatimDisk(drive) => PathBuf::from(format!("{}:", char::from(drive))),
                Prefix::VerbatimUNC(server, share) => {
                    let mut name = OsString::from(r"\\");
                    name.push(server);
                    name.push(r"\");
                    name.push(share);
                    PathBuf::from(name)
                }
                _ => PathBuf::from(prefix.as_os_str()),
            },
            _ => return path.to_path_buf(),
        };
        out.extend(parts);
        out
    }

    #[test]
    fn review_mixed_windows_prefixes_form_relative_urls() -> io::Result<()> {
        let directory = Directory::new("mixed-prefixes", false)?;
        let ordinary = directory.ordinary();
        std::fs::create_dir(ordinary.join("assets"))?;
        println!("NATIVE_WITNESS mixed-prefixes same-directory=true");
        for (target, host) in [
            (directory.0.join("assets/image.svg"), ordinary.join("report.md")),
            (ordinary.join("assets/image.svg"), directory.0.join("report.md")),
        ] {
            assert_eq!(relative_url(&target, &host)?, "assets/image.svg");
        }
        Ok(())
    }

    #[test]
    fn review_ordinary_link_preserves_literal_target() -> io::Result<()> {
        for (suffix, label) in [(" ", "linked-space"), (".", "linked-dot")] {
            let directory = Directory::new(label, false)?;
            let ordinary = directory.ordinary();
            let literal = directory.0.join(format!("assets{suffix}"));
            std::fs::create_dir(&literal)?;
            let link = ordinary.join("linked");
            std::os::windows::fs::symlink_dir(&literal, &link)?;
            std::fs::write(link.join("native.svg"), b"native")?;
            assert_eq!(std::fs::read(literal.join("native.svg"))?, b"native");
            assert!(!ordinary.join("assets").exists());
            println!("NATIVE_WITNESS literal-target suffix={suffix:?} native-write=true");
            let resolved = resolved_directory(&link)?;
            assert_eq!(resolved.canonicalize()?, literal.canonicalize()?);
            std::fs::write(resolved.join("resolved.svg"), b"resolved")?;
            assert_eq!(std::fs::read(literal.join("resolved.svg"))?, b"resolved");
            std::fs::create_dir(literal.join("child"))?;
            let child = resolved_directory(&link.join("child."))?;
            assert_eq!(child.canonicalize()?, literal.join("child").canonicalize()?);
        }
        Ok(())
    }

    #[test]
    fn review_ordinary_trailing_components_use_normalized_urls() -> io::Result<()> {
        for (spelling, label) in [("assets.", "dot-url"), ("assets ", "space-url")] {
            let directory = Directory::new(label, false)?;
            let ordinary = directory.ordinary();
            std::fs::create_dir(ordinary.join("assets"))?;
            std::fs::write(ordinary.join(spelling).canonicalize()?.join("native.svg"), b"native")?;
            assert_eq!(std::fs::read(directory.0.join("assets/native.svg"))?, b"native");
            println!("NATIVE_WITNESS ordinary-normalization spelling={spelling:?} native-write=true");
            assert_eq!(
                relative_url(&ordinary.join(spelling).join("image.svg"), &ordinary.join("report.md"))?,
                "assets/image.svg"
            );
            assert_eq!(
                relative_url(&ordinary.join("future.").join("image.svg"), &ordinary.join("report.md"))?,
                "future/image.svg"
            );
            let literal = directory.0.join(spelling);
            std::fs::create_dir(&literal)?;
            let encoded = if spelling.ends_with(' ') { "assets%20" } else { "assets." };
            assert_eq!(
                relative_url(&literal.join("image.svg"), &directory.0.join("report.md"))?,
                format!("{encoded}/image.svg")
            );
        }
        Ok(())
    }

    #[test]
    fn review_unc_components_use_ordinary_normalization() -> io::Result<()> {
        let directory = Directory::new("unc-normalization", true)?;
        let ordinary = directory.ordinary();
        assert!(matches!(
            directory.0.components().next(),
            Some(Component::Prefix(prefix)) if matches!(prefix.kind(), Prefix::VerbatimUNC(..))
        ));
        std::fs::create_dir(ordinary.join("assets"))?;
        for name in ["assets.", "assets "] {
            std::fs::write(ordinary.join(name).canonicalize()?.join("native.svg"), b"native")?;
            assert_eq!(std::fs::read(directory.0.join("assets/native.svg"))?, b"native");
            println!("NATIVE_WITNESS unc-normalization name={name:?} native-write=true");
            assert_eq!(
                resolved_directory(&ordinary.join(name))?.canonicalize()?,
                directory.0.join("assets").canonicalize()?
            );
            assert_eq!(
                relative_url(&ordinary.join(name).join("image.svg"), &ordinary.join("report.md"))?,
                "assets/image.svg"
            );
        }
        assert_eq!(
            relative_url(&ordinary.join("future.").join("image.svg"), &ordinary.join("report.md"))?,
            "future/image.svg"
        );
        Ok(())
    }
}
