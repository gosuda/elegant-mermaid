use crate::geom::Point;
use crate::scene::PathCommand;

pub(super) const SCALE: i64 = 1_000_000;
const LIMIT: i64 = 1_000_000_000_000;
const BOX: i64 = 1536;
const COMMANDS: &[u8] = b"MLHVCSQTZmlhvcsqtz";

pub(super) type Pair = (i64, i64);

pub(super) fn fixed(text: &str) -> Option<i64> {
    let mut scanner = Scanner::new(text);
    let value = scanner.scan_number()?;
    (scanner.at == scanner.bytes.len()).then_some(value)
}

pub(super) struct Frame {
    pub(super) left: i64,
    pub(super) top: i64,
    pub(super) width: i64,
    pub(super) height: i64,
    pub(super) origin: Point,
}

impl Frame {
    fn scale(&self) -> i64 {
        let side = self.width.max(self.height);
        (div_floor(2 * BOX * SCALE + side, 2 * side)).max(1)
    }

    fn unit(&self, value: i64) -> i64 {
        div_floor(2 * value * self.scale() + SCALE, 2 * SCALE)
    }

    fn point(&self, p: Pair) -> Option<Point> {
        let x = i64::from(self.origin.x) + div_floor(BOX - self.unit(self.width), 2);
        let y = i64::from(self.origin.y) + div_floor(BOX - self.unit(self.height), 2);
        Some(Point {
            x: i32::try_from(x + self.unit(p.0 - self.left)).ok()?,
            y: i32::try_from(y + self.unit(p.1 - self.top)).ok()?,
        })
    }
}

fn div_floor(a: i64, b: i64) -> i64 {
    a.div_euclid(b)
}

pub(super) fn quad_to_cubic(from: Point, control: Point, to: Point) -> PathCommand {
    let third = |a: i32, c: i32| {
        i32::try_from(div_floor(2 * (i64::from(a) + 2 * i64::from(c)) + 3, 6)).unwrap_or(a)
    };
    PathCommand::Curve {
        c1: Point {
            x: third(from.x, control.x),
            y: third(from.y, control.y),
        },
        c2: Point {
            x: third(to.x, control.x),
            y: third(to.y, control.y),
        },
        to,
    }
}

struct Scanner<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Scanner<'a> {
    fn new(text: &'a str) -> Self {
        Scanner {
            bytes: text.as_bytes(),
            at: 0,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.at).copied()
    }

    fn skip_space(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\r' | b'\n' | 0x0c)) {
            self.at += 1;
        }
    }

    fn separators(&mut self) {
        self.skip_space();
        if self.peek() == Some(b',') {
            self.at += 1;
            self.skip_space();
        }
    }

    fn scan_number(&mut self) -> Option<i64> {
        let negative = self.peek() == Some(b'-');
        if matches!(self.peek(), Some(b'+' | b'-')) {
            self.at += 1;
        }
        let mut whole: i64 = 0;
        let mut digits = 0;
        while let Some(d) = self.peek().filter(u8::is_ascii_digit) {
            whole = whole * 10 + i64::from(d - b'0');
            if whole >= SCALE {
                return None;
            }
            digits += 1;
            self.at += 1;
        }
        let mut fraction = 0;
        if self.peek() == Some(b'.') {
            self.at += 1;
            let (value, count) = self.scan_fraction();
            fraction = value;
            digits += count;
        }
        if digits == 0 || matches!(self.peek(), Some(b'e' | b'E')) {
            return None;
        }
        let value = whole * SCALE + fraction;
        Some(if negative { -value } else { value })
    }

    fn scan_fraction(&mut self) -> (i64, usize) {
        let mut value: i64 = 0;
        let mut places = 0;
        while let Some(d) = self.peek().filter(u8::is_ascii_digit) {
            if places < 6 {
                value = value * 10 + i64::from(d - b'0');
            } else if places == 6 && d >= b'5' {
                value += 1;
            }
            places += 1;
            self.at += 1;
        }
        for _ in places..6 {
            value *= 10;
        }
        (value, places)
    }

    fn number(&mut self) -> Option<i64> {
        self.separators();
        let value = self.scan_number()?;
        (value > -LIMIT && value < LIMIT).then_some(value)
    }
}

#[derive(Clone, Copy)]
enum Cmd {
    Move(Pair),
    Line(Pair),
    Curve(Pair, Pair, Pair),
    Quad(Pair, Pair),
    Close,
}

impl Cmd {
    fn in_range(self) -> bool {
        let inside = |p: Pair| p.0 > -LIMIT && p.0 < LIMIT && p.1 > -LIMIT && p.1 < LIMIT;
        match self {
            Cmd::Move(p) | Cmd::Line(p) => inside(p),
            Cmd::Curve(a, b, c) => inside(a) && inside(b) && inside(c),
            Cmd::Quad(a, b) => inside(a) && inside(b),
            Cmd::Close => true,
        }
    }
}

#[derive(Clone, Copy)]
enum Smooth {
    None,
    Cubic(Pair),
    Quad(Pair),
}

fn arity(command: u8) -> Option<usize> {
    match command.to_ascii_uppercase() {
        b'M' | b'L' | b'T' => Some(2),
        b'H' | b'V' => Some(1),
        b'C' => Some(6),
        b'S' | b'Q' => Some(4),
        _ => None,
    }
}

fn follow_up(command: u8) -> u8 {
    match command {
        b'M' => b'L',
        b'm' => b'l',
        b'Z' | b'z' => 0,
        other => other,
    }
}

struct Pen<'a> {
    scanner: Scanner<'a>,
    out: Vec<Cmd>,
    current: Pair,
    start: Pair,
    smooth: Smooth,
}

fn parse(data: &str) -> Option<Vec<Cmd>> {
    let mut pen = Pen {
        scanner: Scanner::new(data),
        out: Vec::new(),
        current: (0, 0),
        start: (0, 0),
        smooth: Smooth::None,
    };
    let mut command = 0u8;
    loop {
        pen.scanner.separators();
        let Some(next) = pen.scanner.peek() else {
            return (!pen.out.is_empty()).then_some(pen.out);
        };
        if COMMANDS.contains(&next) {
            command = next;
            pen.scanner.at += 1;
        }
        if !pen.allowed(command) || !pen.apply(command) {
            return None;
        }
        command = follow_up(command);
    }
}

impl Pen<'_> {
    fn allowed(&self, command: u8) -> bool {
        if self.out.is_empty() {
            return command.eq_ignore_ascii_case(&b'M');
        }
        command != 0
    }

    fn apply(&mut self, command: u8) -> bool {
        let kind = command.to_ascii_uppercase();
        if kind == b'Z' {
            self.out.push(Cmd::Close);
            self.current = self.start;
            self.smooth = Smooth::None;
            return true;
        }
        let Some(count) = arity(kind) else {
            return false;
        };
        let mut args = [0i64; 6];
        for slot in args.iter_mut().take(count) {
            let Some(value) = self.scanner.number() else {
                return false;
            };
            *slot = value;
        }
        if command != kind {
            self.make_absolute(kind, &mut args);
        }
        self.dispatch(kind, args);
        self.out.last().is_some_and(|last| last.in_range())
    }

    fn make_absolute(&self, kind: u8, args: &mut [i64; 6]) {
        match kind {
            b'H' => args[0] += self.current.0,
            b'V' => args[0] += self.current.1,
            _ => {
                for k in 0..arity(kind).unwrap_or(0) / 2 {
                    args[2 * k] += self.current.0;
                    args[2 * k + 1] += self.current.1;
                }
            }
        }
    }

    fn dispatch(&mut self, kind: u8, a: [i64; 6]) {
        match kind {
            b'M' => self.move_to((a[0], a[1])),
            b'L' => self.line_to((a[0], a[1])),
            b'H' => self.line_to((a[0], self.current.1)),
            b'V' => self.line_to((self.current.0, a[0])),
            b'C' => self.cubic_to((a[0], a[1]), (a[2], a[3]), (a[4], a[5])),
            b'S' => self.cubic_to(self.reflected_cubic(), (a[0], a[1]), (a[2], a[3])),
            b'Q' => self.quad_to((a[0], a[1]), (a[2], a[3])),
            _ => self.quad_to(self.reflected_quad(), (a[0], a[1])),
        }
    }

    fn reflected_cubic(&self) -> Pair {
        match self.smooth {
            Smooth::Cubic(c) => (2 * self.current.0 - c.0, 2 * self.current.1 - c.1),
            _ => self.current,
        }
    }

    fn reflected_quad(&self) -> Pair {
        match self.smooth {
            Smooth::Quad(c) => (2 * self.current.0 - c.0, 2 * self.current.1 - c.1),
            _ => self.current,
        }
    }

    fn move_to(&mut self, to: Pair) {
        self.out.push(Cmd::Move(to));
        self.start = to;
        self.current = to;
        self.smooth = Smooth::None;
    }

    fn line_to(&mut self, to: Pair) {
        self.out.push(Cmd::Line(to));
        self.current = to;
        self.smooth = Smooth::None;
    }

    fn cubic_to(&mut self, c1: Pair, c2: Pair, to: Pair) {
        self.out.push(Cmd::Curve(c1, c2, to));
        self.current = to;
        self.smooth = Smooth::Cubic(c2);
    }

    fn quad_to(&mut self, control: Pair, to: Pair) {
        self.out.push(Cmd::Quad(control, to));
        self.current = to;
        self.smooth = Smooth::Quad(control);
    }
}

pub(super) fn convert(data: &str, frame: &Frame) -> Option<Vec<PathCommand>> {
    convert_with(data, |p| frame.point(p))
}

pub(super) fn convert_with(
    data: &str,
    point: impl Fn(Pair) -> Option<Point>,
) -> Option<Vec<PathCommand>> {
    let mut out = Vec::new();
    let mut current = Point { x: 0, y: 0 };
    let mut start = current;
    for cmd in parse(data)? {
        match cmd {
            Cmd::Move(p) => {
                current = point(p)?;
                start = current;
                out.push(PathCommand::Move(current));
            }
            Cmd::Line(p) => {
                current = point(p)?;
                out.push(PathCommand::Line(current));
            }
            Cmd::Curve(a, b, c) => {
                let to = point(c)?;
                out.push(PathCommand::Curve {
                    c1: point(a)?,
                    c2: point(b)?,
                    to,
                });
                current = to;
            }
            Cmd::Quad(control, to) => {
                let to = point(to)?;
                out.push(quad_to_cubic(current, point(control)?, to));
                current = to;
            }
            Cmd::Close => {
                out.push(PathCommand::Close);
                current = start;
            }
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::{Cmd, parse};

    struct Stream(u32);

    impl Stream {
        fn advance(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            self.0 = x;
            x
        }

        fn below(&mut self, n: usize) -> usize {
            usize::try_from(self.advance()).unwrap_or(0) % n
        }

        fn digits(&mut self, count: usize) -> String {
            const ALPHABET: &[u8] = b"0123456789999900005555";
            (0..count)
                .map(|_| char::from(ALPHABET[self.below(ALPHABET.len())]))
                .collect()
        }
    }

    fn round_half_up(a: i128, b: i128) -> i128 {
        (2 * a + b).div_euclid(2 * b)
    }

    fn oracle(sign: &str, whole: &str, fraction: &str) -> (i128, bool) {
        let digits: i128 = format!("{whole}{fraction}").parse().unwrap_or(0);
        let places = u32::try_from(fraction.len()).unwrap_or(0);
        let magnitude = round_half_up(digits * 1_000_000, 10_i128.pow(places));
        let micro = if sign == "-" { -magnitude } else { magnitude };
        (
            micro,
            micro > -1_000_000_000_000 && micro < 1_000_000_000_000,
        )
    }

    fn first_move_x(data: &str) -> Option<i64> {
        match parse(data)?.first() {
            Some(Cmd::Move((x, _))) => Some(*x),
            _ => None,
        }
    }

    #[test]
    fn icon_path_numbers() {
        for i in 1..=2000u32 {
            let mut s = Stream(i);
            let sign = ["", "-", "+"][s.below(3)];
            let whole_len = s.below(9);
            let whole = s.digits(whole_len);
            let fraction_len = s.below(13);
            let mut fraction = s.digits(fraction_len);
            if whole.is_empty() && fraction.is_empty() {
                fraction = s.digits(1);
            }
            let mut text = format!("{sign}{whole}");
            if !fraction.is_empty() || s.below(2) == 0 {
                text.push('.');
                text.push_str(&fraction);
            }
            let (micro, in_range) = oracle(sign, &whole, &fraction);
            let got = first_move_x(&format!("M{text} 0"));
            let want = in_range.then(|| i64::try_from(micro).unwrap_or(0));
            assert_eq!(got, want, "{text:?}");
        }
    }

    #[test]
    fn icon_path_numbers_reject_exponents() {
        for text in ["1e3", "1E3", "1e-3", "2.5e+1", ".5e1"] {
            assert_eq!(first_move_x(&format!("M{text} 0")), None, "{text:?}");
        }
    }

    #[test]
    fn icon_path_coordinates_stay_below_the_limit() {
        for (data, ok) in [
            ("M999999.999999 0", true),
            ("M999999.9999995 0", false),
            ("M1000000 0", false),
            ("M999999 0h1", false),
            ("M999999 0h0.999999", true),
            ("M0 0C999999 0 1000000 0 0 0", false),
            ("M500000 0S0 0 0 0", true),
            ("M0 0C0 0 100000 0 900000 0S0 0 0 0", false),
            ("M-999999 0h-1", false),
        ] {
            assert_eq!(parse(data).is_some(), ok, "{data:?}");
        }
    }
}
