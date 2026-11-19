//! `emd.json` discovery per input directory, with the flag overrides applied.

use super::flags::{Flags, code_list};
use crate::error::CliError;
use crate::{input, paths};
use elegant_mermaid::{LintConfig, lint};
use std::collections::BTreeMap;

pub struct Resolver<'a> {
    flags: &'a Flags,
    by_dir: BTreeMap<String, LintConfig>,
}

impl<'a> Resolver<'a> {
    pub fn new(flags: &'a Flags) -> Self {
        Resolver {
            flags,
            by_dir: BTreeMap::new(),
        }
    }

    /// The configuration for one input: the file found from the input's
    /// directory (or named, or skipped), then `--select` and `--ignore`
    /// replacing the file's lists when given.
    pub fn for_input(&mut self, input: &str) -> Result<LintConfig, CliError> {
        let dir = paths::directory(input);
        let key = if self.flags.config_file.is_empty() && !self.flags.no_config {
            dir.clone()
        } else {
            String::new()
        };
        if !self.by_dir.contains_key(&key) {
            let loaded = self.resolve(&dir)?;
            self.by_dir.insert(key.clone(), loaded);
        }
        let mut config = self.by_dir.get(&key).cloned().unwrap_or_default();
        let select = code_list(&self.flags.select);
        if !select.is_empty() {
            config.select = select;
        }
        let ignore = code_list(&self.flags.ignore);
        if !ignore.is_empty() {
            config.ignore = ignore;
        }
        Ok(config)
    }

    fn resolve(&self, dir: &str) -> Result<LintConfig, CliError> {
        if !self.flags.config_file.is_empty() {
            return load(&self.flags.config_file);
        }
        if self.flags.no_config {
            return Ok(LintConfig::default());
        }
        find(dir)
    }
}

fn load(path: &str) -> Result<LintConfig, CliError> {
    let bytes = std::fs::read(path).map_err(|e| input::read_error(path, e))?;
    Ok(lint::parse_config(path, &String::from_utf8_lossy(&bytes))?)
}

/// Walks up from `dir` to the first `emd.json`, or to the filesystem root.
fn find(dir: &str) -> Result<LintConfig, CliError> {
    let mut at = absolute(dir)?;
    loop {
        let path = paths::join(&at, "emd.json");
        match std::fs::read(&path) {
            Ok(bytes) => {
                return Ok(lint::parse_config(&path, &String::from_utf8_lossy(&bytes))?);
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(input::read_error(&path, e).into()),
        }
        let parent = paths::directory(&at);
        if parent == at {
            return Ok(LintConfig::default());
        }
        at = parent;
    }
}

fn absolute(path: &str) -> Result<String, CliError> {
    if path.starts_with('/') {
        return Ok(paths::clean(path));
    }
    let cwd = std::env::current_dir()?;
    Ok(paths::clean(&format!("{}/{path}", cwd.display())))
}
