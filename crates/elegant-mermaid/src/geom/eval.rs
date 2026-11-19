use std::fmt::{Display, Write};

use super::{
    Axis, GeomError, Point, Rect, Segment, Size, compact, contains, cos_q15, count_inversions,
    inflate, intersects, is_orthogonal, isqrt, place_after, polyline_hits_rect, segments_cross,
    sin_q15, translate, union,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CaseError {
    pub line: usize,
}

impl Display for CaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bad case line {}", self.line)
    }
}

impl std::error::Error for CaseError {}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Operand {
    Int(i64),
    Axis(Axis),
    Tuple(Vec<i64>),
    List(Vec<Operand>),
}

type Handler = fn(&[Operand], &mut String) -> Option<()>;

const OPS: [(&str, Handler); 14] = [
    ("translate", op_translate),
    ("inflate", op_inflate),
    ("union", op_union),
    ("intersects", op_intersects),
    ("contains", op_contains),
    ("place_after", op_place_after),
    ("compact", op_compact),
    ("segments_cross", op_segments_cross),
    ("is_orthogonal", op_is_orthogonal),
    ("polyline_hits_rect", op_polyline_hits_rect),
    ("count_inversions", op_count_inversions),
    ("isqrt", op_isqrt),
    ("sin_q15", op_sin_q15),
    ("cos_q15", op_cos_q15),
];

pub fn eval(input: &str, out: &mut String) -> Result<(), CaseError> {
    for (index, line) in input.split_terminator('\n').enumerate() {
        let failure = CaseError { line: index + 1 };
        let (op, args, result) = split_case(line).ok_or(failure)?;
        if !result_is_valid(result) {
            return Err(failure);
        }
        run(op, &args, out).ok_or(failure)?;
        out.push('\n');
    }
    Ok(())
}

fn split_case(line: &str) -> Option<(&str, Vec<Operand>, &str)> {
    let tokens: Vec<&str> = line.split(' ').collect();
    if tokens.len() < 3 {
        return None;
    }
    let arrow = tokens.len() - 2;
    if tokens[arrow] != "->" {
        return None;
    }
    let op = *tokens.first()?;
    if !is_op_name(op) {
        return None;
    }
    let mut args = Vec::with_capacity(arrow.saturating_sub(1));
    for token in tokens.iter().take(arrow).skip(1) {
        args.push(parse_operand(token)?);
    }
    Some((op, args, *tokens.last()?))
}

fn is_op_name(op: &str) -> bool {
    !op.is_empty()
        && op
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
}

fn result_is_valid(token: &str) -> bool {
    match token {
        "true" | "false" | "overflow" | "domain" => true,
        _ => match parse_operand(token) {
            Some(Operand::Axis(_)) => false,
            Some(_) => true,
            None => false,
        },
    }
}

fn parse_operand(token: &str) -> Option<Operand> {
    match token {
        "X" => Some(Operand::Axis(Axis::X)),
        "Y" => Some(Operand::Axis(Axis::Y)),
        _ => parse_value(token),
    }
}

fn parse_value(token: &str) -> Option<Operand> {
    if let Some(inner) = strip(token, '(', ')') {
        return parse_tuple(inner);
    }
    if let Some(inner) = strip(token, '[', ']') {
        return parse_list(inner);
    }
    parse_int(token).map(Operand::Int)
}

fn strip(token: &str, open: char, close: char) -> Option<&str> {
    let mut chars = token.chars();
    if chars.next() != Some(open) {
        return None;
    }
    if !token.ends_with(close) {
        return None;
    }
    token.get(open.len_utf8()..token.len() - close.len_utf8())
}

fn parse_tuple(inner: &str) -> Option<Operand> {
    let mut values = Vec::new();
    for part in inner.split(',') {
        values.push(parse_int(part)?);
    }
    if values.len() != 2 && values.len() != 4 {
        return None;
    }
    Some(Operand::Tuple(values))
}

fn parse_list(inner: &str) -> Option<Operand> {
    if inner.is_empty() {
        return Some(Operand::List(Vec::new()));
    }
    let mut items = Vec::new();
    for part in split_items(inner) {
        items.push(parse_item(part)?);
    }
    Some(Operand::List(items))
}

fn parse_item(token: &str) -> Option<Operand> {
    if let Some(inner) = strip(token, '(', ')') {
        return parse_tuple(inner);
    }
    parse_int(token).map(Operand::Int)
}

fn split_items(inner: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (index, byte) in inner.bytes().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b',' if depth == 0 => {
                parts.push(inner.get(start..index).unwrap_or(""));
                start = index + 1;
            }
            _ => {}
        }
    }
    parts.push(inner.get(start..).unwrap_or(""));
    parts
}

fn parse_int(token: &str) -> Option<i64> {
    let digits = token.strip_prefix('-').unwrap_or(token);
    if !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if digits.starts_with('0') && token != "0" {
        return None;
    }
    if digits.is_empty() {
        return None;
    }
    let value: i64 = token.parse().ok()?;
    if value < i64::from(i32::MIN) || value > i64::from(i32::MAX) {
        return None;
    }
    Some(value)
}

fn run(op: &str, args: &[Operand], out: &mut String) -> Option<()> {
    let handler = OPS.iter().find(|(name, _)| *name == op).map(|(_, f)| f)?;
    handler(args, out)
}

fn expect_arity(args: &[Operand], count: usize) -> Option<()> {
    if args.len() == count { Some(()) } else { None }
}

fn int32_of(value: i64) -> Option<i32> {
    i32::try_from(value).ok()
}

fn int_arg(op: &Operand) -> Option<i64> {
    match op {
        Operand::Int(value) => Some(*value),
        _ => None,
    }
}

fn axis_arg(op: &Operand) -> Option<Axis> {
    match op {
        Operand::Axis(axis) => Some(*axis),
        _ => None,
    }
}

fn tuple_arg(op: &Operand, arity: usize) -> Option<&[i64]> {
    match op {
        Operand::Tuple(values) if values.len() == arity => Some(values),
        _ => None,
    }
}

fn rect_arg(op: &Operand) -> Option<Rect> {
    let values = tuple_arg(op, 4)?;
    Some(Rect {
        x: int32_of(*values.first()?)?,
        y: int32_of(*values.get(1)?)?,
        w: int32_of(*values.get(2)?)?,
        h: int32_of(*values.get(3)?)?,
    })
}

fn size_arg(op: &Operand) -> Option<Size> {
    let values = tuple_arg(op, 2)?;
    Some(Size {
        w: int32_of(*values.first()?)?,
        h: int32_of(*values.get(1)?)?,
    })
}

fn segment_arg(op: &Operand) -> Option<Segment> {
    let values = tuple_arg(op, 4)?;
    Some(Segment {
        a: Point {
            x: int32_of(*values.first()?)?,
            y: int32_of(*values.get(1)?)?,
        },
        b: Point {
            x: int32_of(*values.get(2)?)?,
            y: int32_of(*values.get(3)?)?,
        },
    })
}

fn point_list_arg(op: &Operand) -> Option<Vec<Point>> {
    let Operand::List(items) = op else {
        return None;
    };
    let mut points = Vec::with_capacity(items.len());
    for item in items {
        let values = tuple_arg(item, 2)?;
        points.push(Point {
            x: int32_of(*values.first()?)?,
            y: int32_of(*values.get(1)?)?,
        });
    }
    Some(points)
}

fn rect_list_arg(op: &Operand) -> Option<Vec<Rect>> {
    let Operand::List(items) = op else {
        return None;
    };
    let mut rects = Vec::with_capacity(items.len());
    for item in items {
        rects.push(rect_arg(item)?);
    }
    Some(rects)
}

fn int_list_arg(op: &Operand) -> Option<Vec<i32>> {
    let Operand::List(items) = op else {
        return None;
    };
    let mut values = Vec::with_capacity(items.len());
    for item in items {
        values.push(int32_of(int_arg(item)?)?);
    }
    Some(values)
}

fn write_rect(out: &mut String, r: &Rect) {
    let _ = write!(out, "({},{},{},{})", r.x, r.y, r.w, r.h);
}

fn write_int(out: &mut String, value: i64) {
    let _ = write!(out, "{value}");
}

fn write_bool(out: &mut String, value: bool) {
    out.push_str(if value { "true" } else { "false" });
}

fn write_error(out: &mut String, error: GeomError) {
    match error {
        GeomError::Overflow => out.push_str("overflow"),
        GeomError::Domain => out.push_str("domain"),
    }
}

fn emit_rect(out: &mut String, result: Result<Rect, GeomError>) {
    match result {
        Ok(r) => write_rect(out, &r),
        Err(e) => write_error(out, e),
    }
}

fn emit_bool(out: &mut String, result: Result<bool, GeomError>) {
    match result {
        Ok(v) => write_bool(out, v),
        Err(e) => write_error(out, e),
    }
}

fn emit_rects(out: &mut String, result: Result<Vec<Rect>, GeomError>) {
    match result {
        Ok(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_rect(out, item);
            }
            out.push(']');
        }
        Err(e) => write_error(out, e),
    }
}

fn emit_int_result(out: &mut String, result: Result<i32, GeomError>) {
    match result {
        Ok(v) => write_int(out, i64::from(v)),
        Err(e) => write_error(out, e),
    }
}

fn op_translate(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 3)?;
    let r = rect_arg(args.first()?)?;
    let dx = int32_of(int_arg(args.get(1)?)?)?;
    let dy = int32_of(int_arg(args.get(2)?)?)?;
    emit_rect(out, translate(r, dx, dy));
    Some(())
}

fn op_inflate(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 2)?;
    let r = rect_arg(args.first()?)?;
    let d = int32_of(int_arg(args.get(1)?)?)?;
    emit_rect(out, inflate(r, d));
    Some(())
}

fn op_union(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 2)?;
    let a = rect_arg(args.first()?)?;
    let b = rect_arg(args.get(1)?)?;
    emit_rect(out, union(a, b));
    Some(())
}

fn op_intersects(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 2)?;
    let a = rect_arg(args.first()?)?;
    let b = rect_arg(args.get(1)?)?;
    emit_bool(out, intersects(a, b));
    Some(())
}

fn op_contains(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 2)?;
    let outer = rect_arg(args.first()?)?;
    let inner = rect_arg(args.get(1)?)?;
    emit_bool(out, contains(outer, inner));
    Some(())
}

fn op_place_after(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 4)?;
    let axis = axis_arg(args.first()?)?;
    let a = rect_arg(args.get(1)?)?;
    let gap = int32_of(int_arg(args.get(2)?)?)?;
    let size = size_arg(args.get(3)?)?;
    emit_rect(out, place_after(axis, a, gap, size));
    Some(())
}

fn op_compact(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 3)?;
    let axis = axis_arg(args.first()?)?;
    let gap = int32_of(int_arg(args.get(1)?)?)?;
    let items = rect_list_arg(args.get(2)?)?;
    emit_rects(out, compact(axis, gap, &items));
    Some(())
}

fn op_segments_cross(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 2)?;
    let s = segment_arg(args.first()?)?;
    let t = segment_arg(args.get(1)?)?;
    emit_bool(out, segments_cross(s, t));
    Some(())
}

fn op_is_orthogonal(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 1)?;
    let points = point_list_arg(args.first()?)?;
    write_bool(out, is_orthogonal(&points));
    Some(())
}

fn op_polyline_hits_rect(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 2)?;
    let points = point_list_arg(args.first()?)?;
    let r = rect_arg(args.get(1)?)?;
    emit_bool(out, polyline_hits_rect(&points, r));
    Some(())
}

fn op_count_inversions(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 1)?;
    let values = int_list_arg(args.first()?)?;
    emit_int_result(out, count_inversions(&values));
    Some(())
}

fn op_isqrt(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 1)?;
    let n = int_arg(args.first()?)?;
    match isqrt(n) {
        Ok(root) => write_int(out, root),
        Err(e) => write_error(out, e),
    }
    Some(())
}

fn op_sin_q15(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 1)?;
    let angle = int32_of(int_arg(args.first()?)?)?;
    write_int(out, i64::from(sin_q15(angle)));
    Some(())
}

fn op_cos_q15(args: &[Operand], out: &mut String) -> Option<()> {
    expect_arity(args, 1)?;
    let angle = int32_of(int_arg(args.first()?)?)?;
    write_int(out, i64::from(cos_q15(angle)));
    Some(())
}

#[cfg(test)]
mod tests {
    use super::{CaseError, eval};
    use crate::geom::Rect;

    fn run(input: &str) -> Result<String, CaseError> {
        let mut out = String::new();
        eval(input, &mut out)?;
        Ok(out)
    }

    fn run_case(line: &str) -> String {
        let mut text = String::from(line);
        text.push('\n');
        match run(&text) {
            Ok(out) => out,
            Err(error) => format!("error {}", error.line),
        }
    }

    #[test]
    fn rect_operations_print_tokens() {
        assert_eq!(
            run_case("translate (0,0,10,10) 5 -7 -> (5,-7,10,10)"),
            "(5,-7,10,10)\n"
        );
        assert_eq!(
            run_case("inflate (10,20,30,40) 2 -> (8,18,34,44)"),
            "(8,18,34,44)\n"
        );
        assert_eq!(run_case("inflate (0,0,3,3) -2 -> domain"), "domain\n");
        assert_eq!(
            run_case("union (0,0,2,2) (5,5,1,1) -> (0,0,6,6)"),
            "(0,0,6,6)\n"
        );
        assert_eq!(
            run_case("intersects (0,0,10,10) (10,0,10,10) -> false"),
            "false\n"
        );
        assert_eq!(run_case("contains (0,0,10,10) (1,1,2,2) -> true"), "true\n");
        assert_eq!(
            run_case("place_after X (0,0,10,20) 3 (4,6) -> (13,0,4,6)"),
            "(13,0,4,6)\n"
        );
        assert_eq!(
            run_case("place_after Y (0,0,10,20) 3 (4,6) -> (0,23,4,6)"),
            "(0,23,4,6)\n"
        );
        assert_eq!(
            run_case("compact X 2 [(10,5,4,4),(0,6,4,4),(12,7,4,4)] -> []"),
            "[(10,5,4,4),(16,6,4,4),(22,7,4,4)]\n"
        );
        assert_eq!(run_case("compact X 0 [] -> []"), "[]\n");
        assert_eq!(run_case("compact X -1 [] -> domain"), "domain\n");
    }

    #[test]
    fn segment_and_polyline_operations_print_tokens() {
        assert_eq!(
            run_case("segments_cross (0,0,0,10) (-5,5,5,5) -> true"),
            "true\n"
        );
        assert_eq!(
            run_case("segments_cross (0,0,3,4) (-5,5,5,5) -> domain"),
            "domain\n"
        );
        assert_eq!(
            run_case("is_orthogonal [(0,0),(4,0),(4,9)] -> true"),
            "true\n"
        );
        assert_eq!(run_case("is_orthogonal [] -> true"), "true\n");
        assert_eq!(
            run_case("polyline_hits_rect [(5,5)] (0,0,10,10) -> true"),
            "true\n"
        );
        assert_eq!(
            run_case("polyline_hits_rect [(0,0),(10,0)] (0,0,10,10) -> false"),
            "false\n"
        );
    }

    #[test]
    fn scalar_operations_print_tokens() {
        assert_eq!(run_case("count_inversions [3,2,1] -> 3"), "3\n");
        assert_eq!(run_case("count_inversions [] -> 0"), "0\n");
        assert_eq!(run_case("isqrt 0 -> 0"), "0\n");
        assert_eq!(run_case("isqrt 9 -> 3"), "3\n");
        assert_eq!(run_case("isqrt -1 -> domain"), "domain\n");
        assert_eq!(run_case("sin_q15 16384 -> 32768"), "32768\n");
        assert_eq!(run_case("sin_q15 49152 -> -32768"), "-32768\n");
        assert_eq!(run_case("sin_q15 0 -> 0"), "0\n");
        assert_eq!(run_case("cos_q15 0 -> 32768"), "32768\n");
        assert_eq!(run_case("cos_q15 -16384 -> 0"), "0\n");
    }

    #[test]
    fn every_line_produces_one_result_line() {
        let input = "isqrt 4 -> 2\nisqrt 16 -> 4\n";
        assert_eq!(run(input), Ok(String::from("2\n4\n")));
        assert_eq!(run(""), Ok(String::new()));
        assert_eq!(run("\n"), Err(CaseError { line: 1 }));
    }

    #[test]
    fn evaluated_values_match_the_kernel() {
        let target = Rect {
            x: 0,
            y: 0,
            w: 10,
            h: 10,
        };
        for index in 0..2000usize {
            let r = Rect {
                x: i32::try_from(index % 40).unwrap_or(0) - 20,
                y: i32::try_from(index % 17).unwrap_or(0) - 8,
                w: i32::try_from(index % 11).unwrap_or(0),
                h: i32::try_from(index % 7).unwrap_or(0),
            };
            let line = format!(
                "intersects ({},{},{},{}) (0,0,10,10) -> true",
                r.x, r.y, r.w, r.h
            );
            let ok = crate::geom::intersects(r, target).unwrap_or(false);
            let expected = format!("{}\n", if ok { "true" } else { "false" });
            assert_eq!(run_case(line.as_str()), expected, "case {index}");
        }
    }
    #[test]
    fn grammar_failures_report_the_line_number() {
        assert_eq!(run("bogus 1 -> 1\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt 4 2\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt 4 -> \n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt 4->4\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt 04 -> 2\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt -0 -> 0\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt +4 -> 2\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt 2147483648 -> 1\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt 4 -> 2147483648\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt 4 -> X\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("ISQRT 4 -> 2\n"), Err(CaseError { line: 1 }));
    }

    #[test]
    fn grammar_failures_reject_wrong_arity() {
        assert_eq!(
            run("isqrt 4 -> 2\nisqrtt 4 -> 2\n"),
            Err(CaseError { line: 2 })
        );
        assert_eq!(run("isqrt 4 -> 2 extra\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt (1,2,3) -> 1\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt (1) -> 1\n"), Err(CaseError { line: 1 }));
        assert_eq!(run("isqrt [] -> 1\n"), Err(CaseError { line: 1 }));
        assert_eq!(
            run("translate (0,0,1,1) 1 -> (1,0,1,1)\n"),
            Err(CaseError { line: 1 })
        );
        assert_eq!(
            run("translate (0,0,1,1) 1 1 1 -> (1,1,1,1)\n"),
            Err(CaseError { line: 1 })
        );
        assert_eq!(run("isqrt 4 -> (1,2,3)\n"), Err(CaseError { line: 1 }));
    }

    #[test]
    fn result_token_is_parsed_but_ignored() {
        assert_eq!(run_case("isqrt 9 -> 4"), "3\n");
        assert_eq!(run_case("isqrt 9 -> (0,0,0,0)"), "3\n");
        assert_eq!(
            run_case("intersects (0,0,1,1) (0,0,1,1) -> false"),
            "true\n"
        );
    }

    #[test]
    fn error_display_is_the_fixed_message() {
        assert_eq!(CaseError { line: 7 }.to_string(), "bad case line 7");
    }
}
