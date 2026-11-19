use super::Mode;

pub const KITTY_QUERY: &[u8] = b"\x1b_Gi=31,s=1,v=1,a=q,t=d,f=24;AAAA\x1b\\";
pub const CELL_SIZE_QUERY: &[u8] = b"\x1b[16t";
pub const DEVICE_QUERY: &[u8] = b"\x1b[c";
pub const FALLBACK_CELL_W: u32 = 8;
pub const FALLBACK_CELL_H: u32 = 16;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Environment<'a> {
    pub kitty_window_id: &'a str,
    pub term: &'a str,
    pub term_program: &'a str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Capability {
    pub kitty_ok: bool,
    pub cell_w: u32,
    pub cell_h: u32,
    pub sixel: bool,
}

impl Default for Capability {
    fn default() -> Self {
        Self {
            kitty_ok: false,
            cell_w: FALLBACK_CELL_W,
            cell_h: FALLBACK_CELL_H,
            sixel: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Replies {
    cell: Option<(u32, u32)>,
    da1: Option<Vec<u32>>,
    kitty: bool,
}

impl Replies {
    pub fn new() -> Self {
        Self {
            cell: None,
            da1: None,
            kitty: false,
        }
    }

    pub fn push(&mut self, reply: &[u8]) -> bool {
        if self.da1.is_some() {
            return true;
        }
        if is_kitty_ok(reply) {
            self.kitty = true;
        } else if let Some(size) = cell_size(reply) {
            self.cell = Some(size);
        } else if let Some(params) = device_attributes(reply) {
            self.da1 = Some(params);
            return true;
        }
        false
    }

    pub fn capability(&self) -> Capability {
        let (cell_w, cell_h) = self.cell.unwrap_or((FALLBACK_CELL_W, FALLBACK_CELL_H));
        let sixel = self.da1.as_ref().is_some_and(|params| params.contains(&4));
        Capability {
            kitty_ok: self.kitty,
            cell_w,
            cell_h,
            sixel,
        }
    }
}

impl Default for Replies {
    fn default() -> Self {
        Self::new()
    }
}

pub fn is_kitty_candidate(env: &Environment<'_>) -> bool {
    !env.kitty_window_id.is_empty()
        || env.term == "xterm-kitty"
        || env.term_program == "ghostty"
        || env.term_program == "WezTerm"
}

pub fn queries(env: &Environment<'_>) -> Vec<u8> {
    let mut out = Vec::new();
    if is_kitty_candidate(env) {
        out.extend_from_slice(KITTY_QUERY);
    }
    out.extend_from_slice(CELL_SIZE_QUERY);
    out.extend_from_slice(DEVICE_QUERY);
    out
}

pub fn choose(env: &Environment<'_>, replies: &Replies) -> Mode {
    let capability = replies.capability();
    if capability.kitty_ok {
        return Mode::Kitty;
    }
    if env.term_program == "iTerm.app" {
        return Mode::Iterm;
    }
    if capability.sixel {
        return Mode::Sixel;
    }
    Mode::Cells
}

fn is_kitty_ok(reply: &[u8]) -> bool {
    reply.starts_with(b"\x1b_G") && reply.windows(7).any(|window| window == b"i=31;OK")
}

fn cell_size(reply: &[u8]) -> Option<(u32, u32)> {
    let body = reply.strip_prefix(b"\x1b[")?.strip_suffix(b"t")?;
    let mut parts = body.split(|byte| *byte == b';');
    match parts.next()? {
        b"6" => {}
        _ => return None,
    }
    let height = parse_decimal(parts.next()?)?;
    let width = parse_decimal(parts.next()?)?;
    if parts.next().is_some() {
        return None;
    }
    match height > 0 && width > 0 {
        true => Some((width, height)),
        false => None,
    }
}

fn device_attributes(reply: &[u8]) -> Option<Vec<u32>> {
    let body = reply.strip_prefix(b"\x1b[?")?.strip_suffix(b"c")?;
    body.split(|byte| *byte == b';')
        .map(parse_decimal)
        .collect()
}

fn parse_decimal(bytes: &[u8]) -> Option<u32> {
    if bytes.is_empty() {
        return None;
    }
    bytes.iter().try_fold(0u32, |value, digit| {
        let digit = u32::from(*digit).checked_sub(u32::from(b'0'))?;
        if digit > 9 {
            return None;
        }
        value.checked_mul(10)?.checked_add(digit)
    })
}

#[cfg(test)]
mod tests {
    use super::{Capability, Environment, Replies, choose, is_kitty_candidate, queries};
    use crate::termgfx::Mode;

    fn env(
        kitty_window_id: &'static str,
        term: &'static str,
        term_program: &'static str,
    ) -> Environment<'static> {
        Environment {
            kitty_window_id,
            term,
            term_program,
        }
    }

    #[test]
    fn kitty_query_leads_only_when_the_candidate_condition_holds() {
        assert_eq!(queries(&env("", "", "")), b"\x1b[16t\x1b[c");
        assert_eq!(queries(&env("", "", "iTerm.app")), b"\x1b[16t\x1b[c");
        for candidate in [
            env("1", "", ""),
            env("", "xterm-kitty", ""),
            env("", "", "ghostty"),
            env("", "", "WezTerm"),
        ] {
            assert!(
                is_kitty_candidate(&candidate),
                "kitty_query_leads_only_when_the_candidate_condition_holds: expected {} to hold (observed false)",
                stringify!(is_kitty_candidate(&candidate))
            );
            assert_eq!(
                queries(&candidate),
                b"\x1b_Gi=31,s=1,v=1,a=q,t=d,f=24;AAAA\x1b\\\x1b[16t\x1b[c"
            );
        }
        assert!(
            !is_kitty_candidate(&env("", "", "iTerm.app")),
            "kitty_query_leads_only_when_the_candidate_condition_holds: expected {} to hold (observed false)",
            stringify!(!is_kitty_candidate(&env("", "", "iTerm.app")))
        );
    }

    #[test]
    fn each_reply_kind_is_parsed() {
        let mut replies = Replies::new();
        assert!(
            !replies.push(b"\x1b_Gi=31;OK\x1b\\"),
            "each_reply_kind_is_parsed: expected {} to hold (observed false)",
            stringify!(!replies.push(b"\x1b_Gi=31;OK\x1b\\"))
        );
        assert_eq!(
            replies.capability(),
            Capability {
                kitty_ok: true,
                cell_w: 8,
                cell_h: 16,
                sixel: false
            }
        );
        assert!(
            !replies.push(b"\x1b[6;20;9t"),
            "each_reply_kind_is_parsed: expected {} to hold (observed false)",
            stringify!(!replies.push(b"\x1b[6;20;9t"))
        );
        assert_eq!(replies.capability().cell_w, 9);
        assert_eq!(replies.capability().cell_h, 20);
        assert!(
            replies.push(b"\x1b[?1;2;4c"),
            "each_reply_kind_is_parsed: expected {} to hold (observed false)",
            stringify!(replies.push(b"\x1b[?1;2;4c"))
        );
        assert!(
            replies.capability().sixel,
            "each_reply_kind_is_parsed: expected {} to hold (observed false)",
            stringify!(replies.capability().sixel)
        );
    }

    #[test]
    fn reply_order_before_da1_does_not_matter() {
        for order in [
            [
                b"\x1b[6;20;9t".as_slice(),
                b"\x1b_Gi=31;OK\x1b\\".as_slice(),
                b"\x1b[?4c".as_slice(),
            ],
            [
                b"\x1b_Gi=31;OK\x1b\\".as_slice(),
                b"\x1b[6;20;9t".as_slice(),
                b"\x1b[?4c".as_slice(),
            ],
        ] {
            let mut replies = Replies::new();
            order.iter().for_each(|reply| {
                replies.push(reply);
            });
            assert_eq!(
                replies.capability(),
                Capability {
                    kitty_ok: true,
                    cell_w: 9,
                    cell_h: 20,
                    sixel: true
                },
                "order {order:?}"
            );
        }
    }
    #[test]
    fn missing_replies_keep_the_fallback_cell_size() {
        let replies = Replies::new();
        assert_eq!(replies.capability(), Capability::default());
        assert_eq!(replies.capability().cell_w, 8);
        assert_eq!(replies.capability().cell_h, 16);
        let mut zero = Replies::new();
        zero.push(b"\x1b[6;0;9t");
        zero.push(b"\x1b[6;20;0t");
        assert_eq!(zero.capability().cell_w, 8);
        assert_eq!(zero.capability().cell_h, 16);
        let mut garbage = Replies::new();
        garbage.push(b"\x1b[6;x;9t");
        garbage.push(b"\x1b[6;9t");
        assert_eq!(garbage.capability(), Capability::default());
    }

    #[test]
    fn mode_choice_table() {
        let cases: [(Capability, &'static str, Mode); 8] = [
            (
                Capability {
                    kitty_ok: true,
                    cell_w: 9,
                    cell_h: 20,
                    sixel: true,
                },
                "iTerm.app",
                Mode::Kitty,
            ),
            (
                Capability {
                    kitty_ok: true,
                    cell_w: 9,
                    cell_h: 20,
                    sixel: false,
                },
                "",
                Mode::Kitty,
            ),
            (
                Capability {
                    kitty_ok: false,
                    cell_w: 8,
                    cell_h: 16,
                    sixel: true,
                },
                "iTerm.app",
                Mode::Iterm,
            ),
            (
                Capability {
                    kitty_ok: false,
                    cell_w: 8,
                    cell_h: 16,
                    sixel: false,
                },
                "iTerm.app",
                Mode::Iterm,
            ),
            (
                Capability {
                    kitty_ok: false,
                    cell_w: 8,
                    cell_h: 16,
                    sixel: true,
                },
                "",
                Mode::Sixel,
            ),
            (
                Capability {
                    kitty_ok: false,
                    cell_w: 8,
                    cell_h: 16,
                    sixel: true,
                },
                "ghostty",
                Mode::Sixel,
            ),
            (
                Capability {
                    kitty_ok: false,
                    cell_w: 8,
                    cell_h: 16,
                    sixel: false,
                },
                "",
                Mode::Cells,
            ),
            (
                Capability {
                    kitty_ok: false,
                    cell_w: 8,
                    cell_h: 16,
                    sixel: false,
                },
                "xterm-kitty",
                Mode::Cells,
            ),
        ];
        for (capability, term_program, want) in cases {
            let mut replies = Replies::new();
            [
                kitty_reply(&capability),
                cell_reply(&capability),
                da1_reply(&capability),
            ]
            .iter()
            .for_each(|reply| {
                replies.push(reply);
            });
            assert_eq!(replies.capability(), capability, "{term_program}");
            assert_eq!(
                choose(&env("", "", term_program), &replies),
                want,
                "{capability:?}"
            );
        }
    }

    fn kitty_reply(capability: &Capability) -> Vec<u8> {
        match capability.kitty_ok {
            true => b"\x1b_Ga=q,i=31;OK\x1b\\".to_vec(),
            false => Vec::new(),
        }
    }

    fn cell_reply(capability: &Capability) -> Vec<u8> {
        match (capability.cell_w, capability.cell_h) {
            (8, 16) => Vec::new(),
            (width, height) => format!("\x1b[6;{height};{width}t").into_bytes(),
        }
    }

    fn da1_reply(capability: &Capability) -> Vec<u8> {
        match capability.sixel {
            true => b"\x1b[?4c".to_vec(),
            false => b"\x1b[?1c".to_vec(),
        }
    }
}
