use super::*;

const ALPHABET: [char; 25] = [
    ' ', '\t', '\n', ':', '-', '#', '[', ']', '{', '}', ',', '\'', '"', '|', '>', '&', '*', '!',
    'a', 'b', 'c', '0', '1', '2', '\\',
];

struct Xs(u32);

impl Xs {
    fn next(&mut self) -> u32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        self.0 = x;
        x
    }

    fn below(&mut self, n: u32) -> u32 {
        self.next() % n
    }
}

fn random_case(i: u32) -> String {
    let mut g = Xs(i.wrapping_add(1));
    let len = 1 + g.below(40);
    let mut s = String::new();
    for _ in 0..len {
        let idx = g.below(25) as usize;
        let Some(c) = ALPHABET.get(idx) else {
            unreachable!("expected Some(c); observed {:?}", ALPHABET.get(idx))
        };
        s.push(*c);
    }
    s
}

fn in_bounds(s: &str, sp: Span) -> bool {
    sp.start <= sp.end
        && sp.end <= s.len()
        && s.is_char_boundary(sp.start)
        && s.is_char_boundary(sp.end)
}

#[test]
fn random_spans_stay_in_range() {
    for i in 0u32..2000 {
        let s = random_case(i);
        let p = preprocess(&s);
        for d in &p.diagnostics {
            assert!(
                in_bounds(&s, d.span),
                "case {i} diag {:?} src {s:?}",
                d.span
            );
        }
        for sp in &p.removed {
            assert!(in_bounds(&s, *sp), "case {i} removed {:?} src {s:?}", sp);
        }
        for d in &p.directives {
            assert!(
                in_bounds(&s, d.body),
                "case {i} body {:?} src {s:?}",
                d.body
            );
        }
    }
}
