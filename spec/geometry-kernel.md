# Geometry kernel

The geometry kernel is the integer geometry library that the Go implementation, the Rust implementation, and the Lean reference share.

## Shared integer rules

- geometry-kernel-01: Go and Rust MUST define `floor_div` and `floor_mod` as shared helpers in the kernel package for every sign of the dividend, and Lean MUST define them as `Int.fdiv` and `Int.fmod`. [just kernel-diff]
- geometry-kernel-02: `floor_div` and `floor_mod` MUST be the floor quotient and the floor remainder, so `floor_mod(x, m)` lies in `[0, m)` for `m > 0`. [just kernel-diff]
- geometry-kernel-03: Kernel code MUST NOT use the truncating `/` or `%` operator on a value that can be negative. [just kernel-diff]
- geometry-kernel-04: Arithmetic on coordinates and on int64 intermediates MUST go through checked helpers that return the overflow error: Go explicit range checks that return `ErrOverflow`, Rust `checked_*` operations, and Lean `Except LayoutError`. [just kernel-diff]
- geometry-kernel-05: Shift counts MUST be constants below 31, and `>>` MUST apply only to a non-negative int64 value that a checked multiply produced. [just kernel-diff]
- geometry-kernel-06: Angles MUST be in units of 1/65536 turn, and a sine argument MUST be reduced with `floor_mod` into `[0, 65536)` before the table lookup. [just kernel-diff]
- geometry-kernel-07: Every sort MUST have a total order whose last key is the declaration index and MUST use the stable sort of the language. [just parity]
- geometry-kernel-08: `max` and `min` MUST resolve ties to the lower declaration index, and adjacency lists MUST keep declaration order. [just parity]
- geometry-kernel-09: Implementations MUST compare fractions such as barycentres and ratios by 64-bit cross-multiplication and MUST NOT compare them by division. [just parity]
- geometry-kernel-10: No iteration over a hash map MUST reach output or an algorithm decision; the Rust core MUST deny `clippy::iter_over_hash_type`, and the Go core MUST iterate slices or sorted keys. [just rust-check]
- geometry-kernel-11: Dumps MUST print integers as minimal ASCII decimal, an optional leading `-`, then digits with no leading zero, no `+`, and no separators; `spec/layout-dump.md` holds the full byte rules. [just parity]
- geometry-kernel-12: Every iterative phase MUST take its iteration cap from `spec/data/layout-constants.json`; reaching a cap MUST keep the best feasible result so far and MUST raise `layout/budget-exhausted` (info), whose registry row is in `spec/data/diagnostics/common.json`. [just parity]
- geometry-kernel-13: Only `render` and `layout` run layout, so only they MUST print `layout/budget-exhausted`, to stderr; `check` and `lint` MUST NOT run layout and MUST NOT print it. [just parity]

## Values

- geometry-kernel-14: A `Point` MUST hold int32 `x` and `y`, and a `Size` MUST hold int32 `w` and `h` with `w >= 0` and `h >= 0`. [just kernel-diff]
- geometry-kernel-15: A `Rect {x, y, w, h}` MUST be valid exactly when `w >= 0`, `h >= 0`, and `x`, `y`, `w`, `h`, `x + w`, and `y + h` are all int32 values. [just kernel-diff]
- geometry-kernel-16: The closed set of a valid Rect MUST be `[x, x+w] x [y, y+h]`, and its interior MUST be `(x, x+w) x (y, y+h)`, which is empty when `w = 0` or `h = 0`. [just kernel-diff]
- geometry-kernel-17: An `Interval {lo, hi}` MUST satisfy `lo <= hi` and MUST be the projection of a Rect on one axis, `[x, x+w]` on `X` and `[y, y+h]` on `Y`; item `i` of `compact` occupies the interval `[p_i, p_i + len_i]` on its axis. [just kernel-diff]
- geometry-kernel-18: `Axis` MUST be the closed enum `X` or `Y`. [just kernel-diff]
- geometry-kernel-19: A `Segment {a, b}` MUST be axis-aligned exactly when `a.x = b.x` or `a.y = b.y`; its open interior is the set of points strictly between `a` and `b`, and it is empty when `a = b`. [just kernel-diff]
- geometry-kernel-20: A `Polyline` MUST be an ordered list of zero or more Points, its segments MUST be the consecutive pairs, and a one-point polyline MUST be one zero-length segment. [just kernel-diff]
- geometry-kernel-21: The kernel MUST define `I32_MIN = -2^31`, `I32_MAX = 2^31 - 1`, and `COORD_LIMIT = 2^29 = 536870912`. [just kernel-diff]

## Predicates

- geometry-kernel-22: `contains(outer, inner)` MUST be inclusive: true exactly when `outer.x <= inner.x`, `inner.x + inner.w <= outer.x + outer.w`, `outer.y <= inner.y`, and `inner.y + inner.h <= outer.y + outer.h`; a Rect contains itself and a Rect that shares its edge. [just kernel-diff]
- geometry-kernel-23: `intersects(a, b)` MUST be true exactly when the open interiors share a point: `max(a.x, b.x) < min(a.x + a.w, b.x + b.w)` and `max(a.y, b.y) < min(a.y + a.h, b.y + b.h)`; a zero-area Rect never intersects. [just kernel-diff]
- geometry-kernel-24: `Disjoint(a, b)` MUST equal `not intersects(a, b)`, so touching Rects are disjoint and a zero-area Rect is disjoint from every Rect. [just kernel-diff]
- geometry-kernel-25: A segment or polyline MUST meet the interior of a Rect `r` exactly when a point of the closed segment lies in the open rectangle `(r.x, r.x + r.w) x (r.y, r.y + r.h)`. [just kernel-diff]
- geometry-kernel-26: `on_boundary(p, r)` MUST be true exactly when `p` lies in the closed `r` and `p.x` is `r.x` or `r.x + r.w`, or `p.y` is `r.y` or `r.y + r.h`. [just kernel-diff]

## Operations

- geometry-kernel-27: Each kernel operation MUST have the case form, the Go signature in `internal/geom`, the Rust signature in the `geom` module, the Lean signature, and the errors of this table. [just kernel-diff]

    |Operation|Case form|Go (`internal/geom`)|Rust (`geom` module)|Lean|Errors|
    |---|---|---|---|---|---|
    |`translate`|`RECT INT INT -> RECT`|`Translate(r Rect, dx, dy int32) (Rect, error)`|`translate(r: Rect, dx: i32, dy: i32) -> Result<Rect, GeomError>`|`Rect.translate : Rect -> Int -> Int -> Except LayoutError Rect`|`domain`: invalid `r`; `overflow`: invalid result|
    |`inflate`|`RECT INT -> RECT`|`Inflate(r Rect, d int32) (Rect, error)`|`inflate(r: Rect, d: i32) -> Result<Rect, GeomError>`|`Rect.inflate : Rect -> Int -> Except LayoutError Rect`|`domain`: invalid `r` or negative result size; `overflow`: invalid result|
    |`union`|`RECT RECT -> RECT`|`Union(a, b Rect) (Rect, error)`|`union(a: Rect, b: Rect) -> Result<Rect, GeomError>`|`Rect.union : Rect -> Rect -> Except LayoutError Rect`|`domain`: invalid input; `overflow`: invalid result|
    |`intersects`|`RECT RECT -> BOOL`|`Intersects(a, b Rect) (bool, error)`|`intersects(a: Rect, b: Rect) -> Result<bool, GeomError>`|`Rect.intersects : Rect -> Rect -> Except LayoutError Bool`|`domain`: invalid input|
    |`contains`|`RECT RECT -> BOOL`|`Contains(outer, inner Rect) (bool, error)`|`contains(outer: Rect, inner: Rect) -> Result<bool, GeomError>`|`Rect.contains : Rect -> Rect -> Except LayoutError Bool`|`domain`: invalid input|
    |`place_after`|`AXIS RECT INT SIZE -> RECT`|`PlaceAfter(axis Axis, a Rect, gap int32, s Size) (Rect, error)`|`place_after(axis: Axis, a: Rect, gap: i32, s: Size) -> Result<Rect, GeomError>`|`Rect.placeAfter : Axis -> Rect -> Int -> Size -> Except LayoutError Rect`|`domain`: invalid `a`, `gap < 0`, negative size; `overflow`: invalid result|
    |`compact`|`AXIS INT [RECT,...] -> [RECT,...]`|`Compact(axis Axis, gap int32, items []Rect) ([]Rect, error)`|`compact(axis: Axis, gap: i32, items: &[Rect]) -> Result<Vec<Rect>, GeomError>`|`compact : Axis -> Int -> List Rect -> Except LayoutError (List Rect)`|`domain`: `gap < 0` or invalid item; `overflow`: any invalid result|
    |`segments_cross`|`SEG SEG -> BOOL`|`SegmentsCross(s, t Segment) (bool, error)`|`segments_cross(s: Segment, t: Segment) -> Result<bool, GeomError>`|`Segment.cross : Segment -> Segment -> Except LayoutError Bool`|`domain`: a segment is not axis-aligned|
    |`is_orthogonal`|`[POINT,...] -> BOOL`|`IsOrthogonal(p []Point) bool`|`is_orthogonal(p: &[Point]) -> bool`|`Polyline.isOrthogonal : List Point -> Bool`|none|
    |`polyline_hits_rect`|`[POINT,...] RECT -> BOOL`|`PolylineHitsRect(p []Point, r Rect) (bool, error)`|`polyline_hits_rect(p: &[Point], r: Rect) -> Result<bool, GeomError>`|`Polyline.hitsRect : List Point -> Rect -> Except LayoutError Bool`|`domain`: invalid `r`, or a coordinate or rect edge outside `±COORD_LIMIT`|
    |`count_inversions`|`[INT,...] -> INT`|`CountInversions(xs []int32) (int32, error)`|`count_inversions(xs: &[i32]) -> Result<i32, GeomError>`|`countInversions : List Int -> Except LayoutError Int`|`overflow`: count above `I32_MAX`|
    |`isqrt`|`INT -> INT`|`Isqrt(n int64) (int64, error)`|`isqrt(n: i64) -> Result<i64, GeomError>`|`isqrt : Int -> Except LayoutError Int`|`domain`: `n < 0`|
    |`sin_q15`|`INT -> INT`|`SinQ15(a int32) int32`|`sin_q15(a: i32) -> i32`|`sinQ15 : Int -> Int`|none|
    |`cos_q15`|`INT -> INT`|`CosQ15(a int32) int32`|`cos_q15(a: i32) -> i32`|`cosQ15 : Int -> Int`|none|

- geometry-kernel-28: `translate(r, dx, dy)` MUST return `(r.x + dx, r.y + dy, r.w, r.h)`. [just kernel-diff]
- geometry-kernel-29: `inflate(r, d)` MUST return `(r.x - d, r.y - d, r.w + 2d, r.h + 2d)`; `d` is added to each of the four sides, and a negative result size is the `domain` error. [just kernel-diff]
- geometry-kernel-30: `union(a, b)` MUST return the smallest Rect that contains both closed Rects, `(m_x, m_y, M_x - m_x, M_y - m_y)` with `m_x = min(a.x, b.x)`, `m_y = min(a.y, b.y)`, `M_x = max(a.x + a.w, b.x + b.w)`, and `M_y = max(a.y + a.h, b.y + b.h)`. [just kernel-diff]
- geometry-kernel-31: The operations `intersects(a, b)` and `contains(outer, inner)` MUST compute the predicates of the same names. [just kernel-diff]
- geometry-kernel-32: `place_after(axis, a, gap, s)` MUST return, on `X`, `(a.x + a.w + gap, a.y, s.w, s.h)` and, on `Y`, `(a.x, a.y + a.h + gap, s.w, s.h)`; the placed Rect starts after the far edge of `a` plus `gap` and aligns with the near edge (top or left) of `a`, and `gap` MUST be `>= 0`. [just kernel-diff]
- geometry-kernel-33: `compact(axis, gap, items)` MUST require `gap >= 0`; with `p_i` the axis coordinate and `len_i` the axis size of `items[i]`, it MUST set `pos_0 = p_0` and `pos_i = max(p_i, pos_{i-1} + len_{i-1} + gap)` for `i >= 1`; output `i` MUST be `items[i]` with its axis coordinate set to `pos_i` and its cross axis unchanged; the output order MUST be the input order; and an empty list MUST give an empty list. [just kernel-diff]
- geometry-kernel-34: `segments_cross(s, t)` MUST be true exactly when the open interiors of `s` and `t` share a point; a zero-length segment MUST give false; perpendicular segments MUST cross exactly when the crossing point lies strictly inside both; collinear segments MUST cross exactly when their open intervals overlap with positive length; touching at an endpoint (end to end, shared endpoint, or T junction) MUST give false; and both segments MUST be axis-aligned. [just kernel-diff]
- geometry-kernel-35: `is_orthogonal(p)` MUST be true exactly when every consecutive pair has equal x or equal y; a zero-length pair counts as orthogonal, a polyline with zero or one point is orthogonal, and this operation MUST have no error case. [just kernel-diff]
- geometry-kernel-36: `polyline_hits_rect(p, r)` MUST be true exactly when some segment of `p` meets the open interior of `r`, and a zero-area `r` MUST give false; with `X0 = r.x`, `X1 = r.x + r.w`, `Y0 = r.y`, and `Y1 = r.y + r.h`, a segment from `p` to `q` misses the interior exactly when one of these holds: [just kernel-diff]

    - `max(px, qx) <= X0`
    - `min(px, qx) >= X1`
    - `max(py, qy) <= Y0`
    - `min(py, qy) >= Y1`
    - `p != q`, with `n = (py - qy, qx - px)`, `c = dot(n, p)`, `m` and `M` the least and greatest of `dot(n, k)` over the four corners `k` of `r`, and `c <= m` or `c >= M`

- geometry-kernel-37: A one-point `polyline_hits_rect` input MUST use the four axis tests only, and the test MUST be exact: it is the separating-axis test for a closed segment and an open rectangle, and its axes are `x`, `y`, and the normal of the segment. [just kernel-diff]
- geometry-kernel-38: `count_inversions(xs)` MUST return the number of index pairs `i < j` with `xs[i] > xs[j]`; equal values MUST NOT count as inversions, and an empty or one-element list MUST give 0. [just kernel-diff]
- geometry-kernel-39: `isqrt(n)` MUST return the largest `m >= 0` with `m * m <= n`. [just kernel-diff]
- geometry-kernel-40: `cos_q15(a)` MUST equal `sin_q15(a + 16384)`, with the sum taken in int64 so it never wraps. [just kernel-diff]

## Errors

- geometry-kernel-41: Every operation argument MUST be int32 by type and every intermediate MUST be int64 (`int64` in Go, `i64` in Rust, `Int` in Lean); under the domain rules every intermediate fits in int64, so an operation SHOULD NOT add a separate intermediate check, and Go and Rust MUST NOT wrap. [just kernel-diff]
- geometry-kernel-42: Domain checks MUST run first, and the result MUST be `domain` exactly when one of these holds: [just kernel-diff]

    - a Rect argument is invalid
    - `place_after` has `gap < 0` or a negative size
    - `compact` has `gap < 0` or an invalid item
    - `inflate` returns a negative size
    - `segments_cross` receives a segment that is not axis-aligned
    - `polyline_hits_rect` receives an invalid `r`, a point coordinate outside `±COORD_LIMIT`, or a rect edge (`x`, `y`, `x + w`, `y + h`) outside `±COORD_LIMIT`
    - `isqrt` receives `n < 0`

- geometry-kernel-43: Otherwise the result MUST be `overflow` when a returned int32 value leaves `[I32_MIN, I32_MAX]`, when a returned Rect is invalid, or when `count_inversions` exceeds `I32_MAX`. [just kernel-diff]
- geometry-kernel-44: `COORD_LIMIT` MUST keep `polyline_hits_rect` exact in int64: each `n` component has magnitude at most `2^30`, each corner coordinate at most `2^29`, so each `dot` term is at most `2^60` and each `dot` value at most `2^61`. [just kernel-diff]
- geometry-kernel-45: Lean MUST use the constructors `LayoutError.overflow` and `LayoutError.domain`, defined in `ElegantGeometry/Basic.lean`; Go MUST use `geom.ErrOverflow` and `geom.ErrDomain`; Rust MUST use `GeomError::Overflow` and `GeomError::Domain`. [just kernel-diff]
- geometry-kernel-46: The case token `overflow` and the case token `domain` MUST be the only error tokens. [just kernel-diff]

## Sine table

- geometry-kernel-47: `tools/specgen` MUST compute the sine table once; for `i` in `0..1024`, `S[i] = round_half_up(32768 * sin(pi * i / 2048))` with `round_half_up(x) = floor(x + 1/2)`, so `S[0] = 0`, `S[1024] = 32768`, and the table has 1025 entries. [just gen-check]
- geometry-kernel-48: `tools/specgen` MUST write `pi` to 60 decimal digits as a constant string, MUST evaluate `sin` by its Taylor series in fixed-point decimal with a `math/big.Int` scaled by `10^60` and truncated after each term, MUST round half up in integer arithmetic, and MUST fail when any scaled value lies within `10^-30` of a half-integer. [just gen-check]
- geometry-kernel-49: The same table MUST be written to `internal/gen/sine.go` (`var SineTable [1025]int32`, exported because `internal/geom` is another package), `crates/elegant-mermaid/src/gen/sine.rs` (`pub(crate) const SINE_TABLE: [i32; 1025]`, in the module declared as `r#gen` because `gen` is a reserved word in edition 2024), and `proofs/Elegant/Gen/Sine.lean` (`def sineTable : Array Int`); no file MUST edit the table by hand. [just gen-check]
- geometry-kernel-50: `sin_q15(a)` MUST accept any int32 `a`, MUST use the angle unit 1/65536 turn, where 16384 is a quarter turn, and MUST compute: [just kernel-diff]

    1. `r = floor_mod(a, 65536)`, so `r` is in `[0, 65535]`.
    2. `q = floor_div(r, 16384)` and `u = r - 16384 * q`, so `u` is in `[0, 16383]`.
    3. `sin_q15 = L(u)` if `q = 0`; `L(16384 - u)` if `q = 1`; `-L(u)` if `q = 2`; `-L(16384 - u)` if `q = 3`.
    4. `L(k)` for `k` in `[0, 16384]`: let `i = floor_div(k, 16)` and `f = k - 16 * i`. If `f = 0`, `L(k) = S[i]`. Otherwise `L(k) = S[i] + floor_div((S[i+1] - S[i]) * f + 8, 16)`.

    The interpolation MUST round half up, and `i + 1 <= 1024` MUST hold whenever `f > 0`.
- geometry-kernel-51: The `sin_q15` result MUST lie in `[-32768, 32768]`, and table entry `S[i]` MUST be the value at angle `16 * i` units. [just kernel-diff]

## Kernel evaluation format

- geometry-kernel-52: `geomcheck eval FILE` and `emd kernel-eval FILE` MUST read the case file `FILE` and write one result line per case to stdout; a case line MUST match this grammar: [just kernel-diff]

    ```
    case-line = op *( SP operand ) SP "->" SP result LF
    op        = 1*( %x61-7A / "_" )          ; one of the 14 names in the operations table
    operand   = int / axis / tuple / list
    axis      = "X" / "Y"
    tuple     = "(" int *( "," int ) ")"     ; arity fixed by the operation: 2 or 4
    list      = "[" [ item *( "," item ) ] "]"
    item      = int / tuple
    result    = int / "true" / "false" / tuple / list / "overflow" / "domain"
    int       = "0" / [ "-" ] %x31-39 *DIGIT  ; int32 range; no "+", no leading zero, no "-0"
    ```

- geometry-kernel-53: Each result MUST be printed as the token of its type: [just kernel-diff]

    |Result type|Token|
    |---|---|
    |int|decimal digits with an optional leading `-`|
    |bool|`true` or `false`|
    |Point|`(x,y)`|
    |Size|`(w,h)`|
    |Rect|`(x,y,w,h)`|
    |Segment|`(x1,y1,x2,y2)`|
    |list|`[item,item]`; `[]` when empty; items use the tokens above|
    |error|`overflow` or `domain`|

- geometry-kernel-54: Each output line MUST be one result token and LF. [just kernel-diff]
- geometry-kernel-55: A line that does not match the grammar, names an unknown op, or has an operand outside int32 MUST make `eval` stop with exit 2 and print `bad case line N` to stderr. [just kernel-diff]
- geometry-kernel-56: `geomcheck eval` and `emd kernel-eval` MUST produce the same bytes for the same input. [just kernel-diff]

## Generated kernel cases

- geometry-kernel-57: `tools/kernelgen` MUST write the cases to stdout, and `just kernel-diff` MUST store them in `corpus/.cache/kernel/cases.txt`: 1000 cases for each of the 14 operations, 14000 lines in all, ordered by operation in the order of the operations table and then by case index `0..999`. [just kernel-diff]
- geometry-kernel-58: For case index `i`, the xorshift32 state MUST start at `x = i + 1`, the generator MUST discard eight outputs, and each draw MUST run `x ^= x << 13; x ^= x >> 17; x ^= x << 5` on uint32 and return `x`. [just kernel-diff]
- geometry-kernel-59: A value draw in range `[lo, hi]` MUST take `s = next()`; when `s mod 16 = 0`, the value MUST be `BOUNDARY[next() mod 5]` with `BOUNDARY = [-2147483648, -1, 0, 1, 2147483647]`; otherwise the value MUST be `lo + (next() mod (hi - lo + 1))`. [just kernel-diff]
- geometry-kernel-60: The draw ranges MUST be `COORD` `[-1000, 1000]`, `SIZE` `[-5, 500]`, `GAP` `[-5, 50]`, `DELTA` `[-300, 300]`, `ANGLE` `[-200000, 200000]`, `VAL` `[-50, 50]`, and `N` `[-5, 100000]`. [just kernel-diff]
- geometry-kernel-61: An `AXIS` MUST be `X` when `next() mod 2 = 0`, else `Y`, and a list length MUST be `next() mod 7`. [just kernel-diff]
- geometry-kernel-62: `RECT` MUST be `COORD` x, `COORD` y, `SIZE` w, `SIZE` h; `POINT` MUST be `COORD` x, `COORD` y; `SEG` MUST be `COORD` x1, `COORD` y1, then `b = next() mod 2`, where `b = 0` gives a horizontal segment (`y2 = y1`, then `COORD` x2) and `b = 1` gives a vertical segment (`x2 = x1`, then `COORD` y2); a `SIZE` MUST be two `SIZE` draws. [just kernel-diff]
- geometry-kernel-63: Operands MUST be drawn in case-form order, one list entry per operation: [just kernel-diff]

    - `translate`: RECT, DELTA, DELTA
    - `inflate`: RECT, DELTA
    - `union`: RECT, RECT
    - `intersects`: RECT, RECT
    - `contains`: RECT, RECT
    - `place_after`: AXIS, RECT, GAP, SIZE
    - `compact`: AXIS, GAP, length, RECT per item
    - `segments_cross`: SEG, SEG
    - `is_orthogonal`: length, POINT per item
    - `polyline_hits_rect`: length, POINT per item, RECT
    - `count_inversions`: length, VAL per item
    - `isqrt`: N
    - `sin_q15`: ANGLE
    - `cos_q15`: ANGLE

## Ties between implementations

- geometry-kernel-64: `just kernel-diff` MUST run `go run ./tools/kernelgen > corpus/.cache/kernel/cases.txt`, then run `geomcheck eval`, `bin/emd-go kernel-eval`, and `bin/emd-rs kernel-eval` on that file, and MUST fail on any byte difference (`cmp`). [just kernel-diff]
- geometry-kernel-65: Go unit tests MUST NOT call Lean and MUST use naive in-language oracles. [just go-check]
- geometry-kernel-66: Rust unit tests MUST NOT call Lean and MUST use naive in-language oracles. [just rust-check]
- geometry-kernel-67: `just validate` MUST pipe every corpus layout dump from both implementations through `geomcheck validate`; the validator clauses and `HardConstraints` are in `spec/layout-dump.md`. [just validate]
