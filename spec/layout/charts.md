# Chart layout family

This file defines the chart family: its entry points, its model payloads, its shared scales, its eleven kinds, and its proofs.

## Entry and inputs

- charts-01: The Go entry point MUST be `func Layout(ctx context.Context, m *model.Chart, o layout.Options) (*scene.Scene, error)` in package `internal/layout/chart`. [just build]
    Rust: `pub fn layout(m: &model::Chart, o: &layout::Options) -> Result<scene::Scene, LayoutError>` in module `layout::chart`.
- charts-02: The family options MUST carry the resolved profile, limits, and theme. [just lean-parity]
    Charts ignore `thoroughness` and `max_width`.
- charts-03: The model MUST hand the family a `Kind`, one of `gantt`, `xychart`, `quadrant`, `treemap`, `wardley`, `pie`, `radar`, `sankey`, `venn`, `cynefin`, and `info`, a `Title`, the honoured config keys of the kind, and exactly one payload that matches `Kind`. [just lean-parity]
    The honoured config keys of a kind are the rows of `spec/data/config-keys/<kind>.json`.
- charts-04: The Gantt payload MUST hold these fields. [just lean-parity]
    `Sections` (name, declaration index). `Tasks` (section, name, `Start` and `End` as seconds since 1970-01-01 00:00:00 with no zone, `Milestone`). `Excludes`. `Includes`. `AxisFormat`. `DateFormat` (the `dateFormat` directive as text; empty when the source has none, `ganttDb.js:25`, set at `ganttDb.js:101-103`). `TickInterval`. `Weekday`. `Weekend`. `TodayMarker`, which is used only for the diagnostic.
- charts-05: The XY payload MUST hold `XCategories` (a band) or `XDomain{Min, Max}`, `YDomain{Min, Max}`, and the `Bars` and `Lines` series of values. [just lean-parity]
- charts-06: The Quadrant payload MUST hold the four quadrant labels, two axis label pairs, and `Points` (name, `x` and `y` in thousandths in 0 to 1000, class). [just lean-parity]
- charts-07: The Treemap payload MUST hold a tree of `Node{Name, Value, Children, Index}`, where `Index` is the declaration index. [just lean-parity]
- charts-08: The Wardley payload MUST hold `Components` (name, `x` and `y` in thousandths of 0 to 100, `Index`) and `Links`. [just lean-parity]
- charts-09: The Pie payload MUST hold `Sections` (label, value, `Index`) and `ShowData`. [just lean-parity]
- charts-10: The Radar payload MUST hold `Axes` (label), `Curves` (name, values), `Min`, `Max` (absent means the largest value), `Ticks`, and `Graticule`. [just lean-parity]
- charts-11: The Sankey payload MUST hold `Nodes` (id, `Index`) and `Links` (source, target, value, `Index`). [just lean-parity]
- charts-12: The Venn payload MUST hold `Sets` (name, size, `Index`) and `Overlaps` (`A` and `B` set indices, value; an absent pair is 0). [just lean-parity]
- charts-13: The Cynefin payload MUST hold five domains (name, items) and `Transitions`. [just lean-parity]
- charts-14: The Info payload MUST hold `Version`, the constant `Version` of package `mermaid` (`"0.1.0"`). [just lean-parity]

## Numbers, units, and angles

- charts-15: The model MUST store each numeric literal as an `int64` in thousandths, with `chart.number_scale` equal to 1000. [just lean-parity]
    A literal with more than three fractional digits rounds half away from zero. A value or domain span above 2^31 - 1 thousandths returns `ErrOverflow`.
- charts-16: Vector values MUST be in units of 1/64 px, and cell values MUST be in cells. [just lean-parity]
- charts-17: The kinds `pie`, `radar`, `sankey`, and `venn`, and the line plots of `xychart`, MUST be drawn by the braille raster of `spec/render-cells.md`, and their geometry constants MUST be in vector units. [just lean-parity]
    That rule reads the vector scene. This family does not restate the dot sampling rule. Bars of `xychart` keep the cell rule.
- charts-18: Angles MUST be in 1/65536 turns, with the origin at 12 o'clock and angles growing clockwise. [just lean-parity]
    d3-shape 3.2.0 `src/arc.js` sets `a0 = startAngle - halfPi`, so an angle `θ` gives `x = r sin θ` and `y = -r cos θ`. `src/pie.js` defaults `startAngle` to 0 and `endAngle` to `τ`, so slices start at 12 o'clock and run clockwise.
- charts-19: The integer helpers MUST be `floor_div`, `ceil_div`, `floor_mod`, `isqrt`, `sin_q15`, and `cos_q15`, exactly as `spec/geometry-kernel.md` defines them, including its table, reduction, and interpolation rules. [just kernel-diff]
    This family adds no trigonometric rule of its own. Go and Rust MUST NOT use floats in this path.

## Scales

- charts-20: The linear scale MUST map a value as `map(v) = r0 + floor_div((v - d0) * (r1 - r0), d1 - d0)`. [just lean-parity]
    When `d1 = d0`, every value maps to `floor_div(r0 + r1, 2)`, the midpoint of the range. d3 `continuous.js` (`normalize`) returns 0.5 for a zero-width domain, which gives the same midpoint. The domain span is at most 2^31 - 1, and the range span is at most `chart.range_units_max` (4194304), so the product fits in `int64`.
- charts-21: The band scale MUST place `n` categories over range `R` by these rules. [just lean-parity]
    `step = floor_div(R, max(1, n - 1))`. For `n >= 2`, category `k` sits at `floor_div(k * R, n - 1)`. For `n = 1`, category 0 sits at `floor_div(R, 2)`. The bandwidth is 0.
    d3-scale 4.0.2 `src/band.js` (`rescale`) sets `step = R / max(1, n - paddingInner + 2 * paddingOuter)`, which is `R / max(1, n - 1)` here, with `paddingInner(1)`, `paddingOuter(0)`, and `align(0.5)`; it offsets the first band by `(R - step * (n - 1)) * align`, which is 0 for `n >= 2`. The read sites are `xychart/chartBuilder/components/axis/bandAxis.ts:31-34`. Bar widths come from the xychart bar rule.
- charts-22: The tick rule MUST take `lo` and `hi` as the domain ends in thousandths, set `D = |hi - lo|` and `C = chart.tick_count` (10), and run these steps in order. [just lean-parity]
    1. If `D = 0`, the only tick is `lo`.
    2. If `D < C`, the step is 1 unit. A sub-unit step rounds up to 1 unit.
    3. Otherwise find the largest `e >= 0` with `10^e * C <= D`, and set `p = 10^e`.
    4. Let `S2 = C^2 * p^2` (`u128`). If `D^2 >= 50 * S2`, the step is `10 * p`. Else if `D^2 >= 10 * S2`, the step is `5 * p`. Else if `D^2 >= 2 * S2`, the step is `2 * p`. Else the step is `p`. These compare the squares of `error >= sqrt(50)`, `sqrt(10)`, `sqrt(2)`, where `error = D / (C * p)`.
    5. The ticks are `v = ceil_div(min(lo, hi), step) * step`, then `v + step`, and so on while `v <= max(lo, hi)`. If `lo > hi`, reverse the list.
    d3-array 3.2.4 `src/ticks.js` (`tickSpec`) sets `step = (stop - start) / count`, `power = floor(log10(step))`, and `error = step / 10^power`. The factor is 10, 5, 2 or 1 when `error` is at least `sqrt(50)`, `sqrt(10)`, `sqrt(2)`, or less. For `power >= 0`, which is `D >= C`, the increment is `factor * 10^power`, as in steps 3 and 4. For `D < C`, d3 gives a fractional increment; the port uses 1 unit instead (step 2). The read site is `linearAxis.ts:24`.
- charts-23: The tick scan MUST be the only loop of the rule, MUST recurse on fuel `chart.scan_cap` (40, the exponents 0 to 19), and MUST emit at most `chart.tick_cap` (64) ticks. [just lean-parity]
    A longer list keeps the first 64 and raises `layout/budget-exhausted` (info).

## Gantt

- charts-24: Civil dates MUST use `days_from_civil(y, m, d)` and `civil_from_days(z)`: integer, proleptic Gregorian, with day 0 equal to 1970-01-01. [just lean-parity]
    Seconds are `days * 86400 + hh * 3600 + mm * 60 + ss`.
- charts-25: The ISO weekday MUST be `floor_mod(days + 3, 7) + 1`, so 1 is Monday. [just lean-parity]
- charts-26: The core MUST use the integer civil-date functions in both languages, and Go `time` and the Rust in-house functions MUST agree on the corpus. [just go-check]
    Go tests check the integer functions against `time`. Dates are naive, with no zone. The core never reads the clock.
- charts-27: The Gantt auto tick interval MUST choose from this duration table in seconds, with `span = max_end - min_start` and `C = chart.tick_count`. [just lean-parity]
    The target is `span / C` seconds, kept exact and never rounded. The table is: 1, 5, 15, 30, 60, 300, 900, 1800, 3600, 10800, 21600, 43200, 86400, 172800, 604800, 2592000 (30 days), 7776000 (90 days), 31536000 (365 days).
    The table matches d3-time 3.1.0 `src/ticks.js` (`tickIntervals`, which `d3-scale` 4.0.2 `src/time.js` reaches through `timeTicks`). d3 uses milliseconds below the first entry and `year.every(tickStep(...))` above the last. The port clamps to the first or last entry instead.
- charts-28: The interval index MUST follow this rule. [just lean-parity]
    Let `i` be the first index with `s[i] * C > span`, or 18 when none. If `i = 0`, use index 0. If `i = 18`, use index 17. Otherwise, if `span^2 < C^2 * s[i-1] * s[i]` (`u128`), use `i - 1`; else use `i`. This is the d3-time choice: `tickInterval` in `src/ticks.js` compares `target / s[i-1]` with `s[i] / target`, and the target stays exact here.
- charts-29: Gantt ticks MUST fall on field multiples by these rules. [just lean-parity]
    Seconds, minutes, and hours fall on multiples of the field. Days fall on multiples of `(day-of-month - 1)`. Weeks start on `Weekday` (default `sunday`, `ganttDb.js:41` and the `GanttDiagramConfig` `weekday` key). Months and years use the month of year.
    d3-time 3.1.0 `every(n)` (`src/interval.js`) keeps dates where `field(d) % n === 0`. The fields are the seconds (`second.js`), minutes (`minute.js`) and hours (`hour.js`) of the time, the day of month minus 1 (`day.js`), and the month of year with January as 0 (`month.js`). Weeks have no field, so `every` keeps week starts where `interval.count(0, d) % n === 0`, which counts weeks from the week start on or before 1970-01-01 (`week.js`).
- charts-30: An explicit `tickInterval` MUST match `^([1-9]\d*)(millisecond|second|minute|hour|day|week|month)$`. [just lean-parity]
    The read site is `ganttRenderer.js:665`. `millisecond` is not supported: emit `gantt/tick-interval-unsupported` (warning) and use the auto rule.
- charts-31: Gantt axis labels MUST use `AxisFormat` when it is set. [just lean-parity]
    Else use `%d` when `dateFormat` is `D`. Else use `%Y-%m-%d`. Only the exact text `D` selects `%d`; the match is case-sensitive, and no other `DateFormat` value selects it (`ganttRenderer.js:650-659`, `:655`). The supported codes are `%Y %m %d %H %M %S %a %b %%`. Any other code emits `gantt/axis-format-unsupported` (warning) and `%Y-%m-%d` is used.
- charts-32: A day MUST be excluded when one of these holds. [just lean-parity]
    Its ISO weekday is in the weekend. The weekend starts at `WEEKEND_START_DAY[Weekend]` and spans two days. The default is `saturday` (`let weekend = 'saturday'` in `ganttDb.js`), which gives ISO days 6 and 7. `friday` gives days 5 and 6 (`WEEKEND_START_DAY = { friday: 5, saturday: 6 }` in `ganttDb.js`). The weekend applies only when `Excludes` contains the token `weekends` (`isInvalidDate` in `ganttDb.js`). Or its weekday name is in `Excludes`. Or its date, as `YYYY-MM-DD`, is in `Excludes`.
    A date in `Includes` is never excluded. This precedence is ours.
- charts-33: Excluded days MUST NOT count toward a task's day duration, and each excluded day MUST draw a shaded column from its start to the next day start. [just lean-parity]
    A bar covers the excluded days inside its span. The read site is `drawExcludeDays`, `ganttRenderer.js:547`.
- charts-34: Gantt rows MUST follow declaration order, with one header row for each section and one row for each task under its section. [just lean-parity]
    The row pitch is `gantt.bar_height + gantt.row_gap`. `gantt.bar_height` is 20 px / 2 cells (upstream `barHeight`, default 20). `gantt.row_gap` is 4 px / 1 cell (upstream `barGap`, default 4). Row `k` starts at `gantt.top_pad + k * pitch`. `gantt.top_pad` is 50 px / 4 cells (upstream `topPadding`, default 50).
- charts-35: The Gantt time map MUST use the domain `[min start, max end]` over all tasks and the range `[gantt.label_gutter, W - gantt.side_pad]`. [just lean-parity]
    `gantt.label_gutter` is 75 px / 10 cells (upstream `leftPadding`, default 75). `gantt.side_pad` is 75 px / 10 cells (upstream `rightPadding`, default 75). `W` is `gantt.width`, which is 1200 px / 150 cells. The gantt schema has no width default, and `useWidth` has no default (base config, `config.schema.yaml` line 481), so the renderer fallback of 1200 applies (`ganttRenderer.js:105-113`). Upstream reads the container width first; this plan does not read it. With no tasks, the domain is `[0, 86400]`.
- charts-36: A Gantt bar MUST be `x0 = map(start)`, `x1 = map(end)`, with width `x1 - x0`, and a milestone MUST be `x0 = map(start) + floor_div(map(end) - map(start), 2) - floor_div(gantt.bar_height, 2)` with width `gantt.bar_height`. [just lean-parity]
    The read sites are `ganttRenderer.js:296-319` for the bar and `:407-410` for the milestone.
- charts-37: The Gantt canvas height MUST be `gantt.top_pad + rows * pitch + gantt.axis_height`, with `gantt.axis_height` equal to 50 px / 4 cells. [just lean-parity]
    The date axis sits in the band under the last row. Upstream draws the grid group at `h - 50` (`ganttRenderer.js` makeGrid).
- charts-38: The family MUST ignore `todayMarker`, MUST draw nothing for it, and MUST emit `gantt/today-marker-ignored` (info) at the marker's span. [just lean-parity]
    The core never reads the clock.

## XY chart

- charts-39: The xychart canvas MUST be `xychart.width` by `xychart.height`, which are 700 px / 88 cells by 500 px / 32 cells (upstream defaults `width` 700 and `height` 500, `XYChartConfig`), and the plot MUST take `xychart.plot_reserved_percent` (50) of the full canvas width and height, rounded down. [just lean-parity]
    The renderer sizes the SVG from these values and reads no container width (`xychartRenderer.ts:35-43`). The available width and height are `xychart.width` and `xychart.height` with nothing subtracted (`orchestrator.ts:62-63`, `:67-69`). So the reserved plot width is `floor_div(xychart.width * 50, 100)` = 350 px / 44 cells, and the reserved plot height is `floor_div(xychart.height * 50, 100)` = 250 px / 16 cells. `plotReservedSpacePercent` has `default: 50` and `minimum: 30` in `XYChartConfig`.
- charts-40: The xychart bar width MUST be `bw = floor_div(min(2 * outer, tickDist) * (1000 - xychart.bar_padding_m), 1000)`, with `xychart.bar_padding_m` equal to 50, and the half width MUST be `floor_div(bw, 2)`. [just lean-parity]
    `tickDist` is `floor_div(R - 2 * outer, n)`, where `R` is the x plot width, `outer` is the current x outer padding, and `n` is the number of x tick values (`baseAxis.ts:68-71`, `getTickDistance`). `tickDist` is not the band step, which places the category positions. The read site is `barPlot.ts:20-24`. The bar width uses `tickDist` and `outer` after the bar outer rule.
- charts-41: The bar outer padding MUST be raised once, after the label rule, and only when the chart has a bar plot. [just lean-parity]
    If `xychart.bar_width_ratio_m * tickDist > 2000 * outer`, then `outer = floor_div(700 * tickDist, 2000)`. `xychart.bar_width_ratio_m` is 700 per mille, that is 0.7 (upstream `BAR_WIDTH_TO_TICK_WIDTH_RATIO`, `baseAxis.ts:12`), and the literal 700 is this value. `tickDist` here uses the outer from the label rule. When the condition is false, `outer` keeps the label value. The read sites are `baseAxis.ts:12`, `:85-86`, and the end of `calculateVerticalSpace` in `orchestrator.ts`.
- charts-42: The label outer padding MUST be `outer = min(floor_div(labelW, 2), floor_div(xychart.label_outer_max_m * avail, 1000))`, with `xychart.label_outer_max_m` equal to 200. [just lean-parity]
    `outer` is 0 before this rule (`baseAxis.ts:23`). This rule sets `outer` only when the x-axis `showLabel` setting is true (`baseAxis.ts:97`, `:98-100`); otherwise `outer` stays 0. `labelW` is the widest x tick label, measured in profile units at the x-axis `labelFontSize` (14 px, the `XYChartAxisConfig` default). The model stage measures it, since a family never measures text; the rule is `spec/text-measurement.md`. `avail` is the width the x axis receives: `xychart.width` minus the reserved plot width (`orchestrator.ts:75`, `:86`), which is 350 px / 44 cells.
- charts-43: xychart line plots MUST take their x and y from the band and linear scales, and the cell profile MUST draw them as braille. [just lean-parity]

## Quadrant

- charts-44: The quadrant canvas MUST be `quadrant.width` by `quadrant.height`, which are 500 px / 63 cells by 500 px / 32 cells (upstream defaults `chartWidth` and `chartHeight`, 500 each, `QuadrantChartConfig`). [just lean-parity]
    The renderer reads them and no container width (`quadrantRenderer.ts:49-50`).
- charts-45: The quadrant plot rectangle MUST be inset by `quadrant.padding` on every side, by `quadrant.axis_band` on the left and bottom when axis labels show, and by `quadrant.title_band` on top when the title shows. [just lean-parity]
    `quadrant.padding` is 5 px / 1 cell (upstream `quadrantPadding`, default 5). `quadrant.axis_band` is 26 px. The left band is 4 cells wide and the bottom band is 2 rows high, by the unit rule per axis. Its value is `2 * yAxisLabelPadding + yAxisLabelFontSize` for the left band and `2 * xAxisLabelPadding + xAxisLabelFontSize` for the bottom band, which are both 2 * 5 + 16 with the upstream defaults (`quadrantBuilder.ts`, `calculateSpace`). `quadrant.title_band` is 40 px / 3 cells, which is `titleFontSize + 2 * titlePadding` = 20 + 2 * 10.
- charts-46: A quadrant point MUST map as `x_px = plotL + floor_div(x * plotW, 1000)` and `y_px = plotT + plotH - floor_div(y * plotH, 1000)`, so the y axis is inverted. [just lean-parity]
    The read site is `quadrantBuilder.ts`, `xAxis` and `yAxis` over `[0, 1]`.
- charts-47: Quadrant points MUST be clamped to 0 to 1000 thousandths. [just lean-parity]
    d3-scale 4.0.2 `src/continuous.js` leaves `clamp` off by default, so `scaleLinear` extrapolates outside its domain. This family clamps so that every point stays inside the plot.
- charts-48: A quadrant marker MUST be a circle of radius `quadrant.point_radius`, which is 5 px / 1 cell, at `(x_px, y_px)`, with its label at `x_px + radius + quadrant.point_text_pad` on the baseline `y_px`. [just lean-parity]
    `quadrant.point_radius` is the upstream `pointRadius`, default 5. `quadrant.point_text_pad` is 5 px / 1 cell (upstream `pointTextPadding`, default 5). Labels are not moved. There is no collision avoidance in this version.

## Wardley

- charts-49: The Wardley plot MUST be inset by `wardley.padding` on each side, with `W = wardley.width` and `H = wardley.height`. [just lean-parity]
- charts-50: A Wardley coordinate `v`, in thousandths of 0 to 100, MUST map as `x_px = pad + floor_div(v * (W - 2 * pad), 100000)` and `y_px = H - pad - floor_div(v * (H - 2 * pad), 100000)`, and a value outside 0 to 100000 thousandths MUST be clamped to that range. [just lean-parity]
    The read site is `wardleyRenderer.ts`, `projectX` and `projectY`.
- charts-51: Wardley labels MUST follow the quadrant label rule, and the family MUST NOT move a label to avoid a collision. [just lean-parity]

## Cynefin

- charts-52: The cynefin frame MUST be `cynefin.width` by `cynefin.height`, which are 800 px / 100 cells by 600 px / 38 cells, with `cx = floor(W / 2)` and `cy = floor(H / 2)`. [just lean-parity]
    The upstream defaults are 800 and 600 (`CynefinDiagramConfig`); `cynefinRenderer.ts:83-84` reads them.
- charts-53: The four cynefin domain rectangles MUST be `complex` at `(0, 0, hw, hh)`, `complicated` at `(hw, 0, hw, hh)`, `chaotic` at `(0, hh, hw, hh)`, and `clear` at `(hw, hh, hw, hh)`, with `hw = floor(W / 2)` and `hh = floor(H / 2)`. [just lean-parity]
    The read site is `getDomainLayouts`, `cynefinRenderer.ts:40-50`.
- charts-54: The confusion ellipse MUST be centred at `(cx, cy)`, with `rx = floor_div(W * cynefin.confusion_permille, 1000)` and `ry = floor_div(H * cynefin.confusion_permille, 1000)`, where `cynefin.confusion_permille` is 150. [just lean-parity]
    It is one `Ellipse` item, drawn by the Ellipse rule of `spec/render-cells.md`. The read site is the comment at `cynefinRenderer.ts:157`.
- charts-55: The cynefin cliff MUST be an S-curve of two cubic segments from `(cx, cy)` down to `(cx, H)`, with `A = floor_div(W * 3, 100)` and `dh = H - cy`. [just lean-parity]
    Segment 1 is `C (cx + A, cy + floor_div(dh * 20, 100)) (cx - floor_div(3 * A, 2), cy + floor_div(dh * 55, 100)) (cx + floor_div(A, 2), cy + floor_div(dh * 75, 100))`. Segment 2 is `C (cx - A, cy + floor_div(dh * 85, 100)) (cx + floor_div(3 * A, 10), cy + floor_div(dh * 95, 100)) (cx, H)`.
    Upstream `generateCliffPath` (`cynefinBoundaries.ts:135-150`) uses `topY = height * 0.5` and `width * 0.03`; the port uses `cy = floor(H / 2)` and `A = floor_div(W * 3, 100)`. In cells it is drawn as dots by item 5 of the per-primitive rule of `spec/render-cells.md`.
- charts-56: The cynefin fold MUST be a wavy vertical boundary at `x = cx` from `y = 0` to `y = H`, seeded by one xorshift32 generator per diagram. [just lean-parity]
    Seed `s0` is the configured `seed` when it is non-zero, as a `uint32`; otherwise `cynefin.default_seed` = `0x2545F491`. Upstream hashes the element id here (`cynefinBoundaries.ts:32-40`), which is not deterministic, so this family replaces it. The generator is xorshift32 with shift triple 13, 17, 5: each step is `s ^= s << 13; s ^= s >> 17; s ^= s << 5` on `uint32` with wrapping, and the output is the new `s`.
- charts-57: The fold generator MUST draw exactly 15 values per diagram, in this order: eight jitters for points `i` = 0 to 7, then seven control offsets for segments `i` = 0 to 6. [just lean-parity]
    Amplitude `A` is the `boundaryAmplitude` config value in units when set. Otherwise `A = floor_div(W * cynefin.amplitude_permille, 1000)`, with `cynefin.amplitude_permille` equal to 15, which is 1.5 percent of the width (upstream uses the same 1.5 percent, `cynefinBoundaries.ts:58`).
- charts-58: Fold point `i` MUST be `x_i = cx + floor_div(u_i * 2A, 2^32) - A` and `y_i = floor_div(i * H, cynefin.wave_segments)`, with `cynefin.wave_segments` equal to 7. [just lean-parity]
    Segment `i` has `dir = +1` for even `i` and `-1` for odd `i`, and `off = dir * floor_div(3 * A * u'_i, 2^33)`, where `u'_i` is the draw for segment `i`. `midY = floor_div(y_i + y_{i+1}, 2)`. The control points are `(x_i + off, midY)` and `(x_{i+1} - off, midY)`.
    Vector: `M x0,y0`, then one `C` command per segment. Cell: a polyline through the eight points, drawn as dots by item 5 of the per-primitive rule of `spec/render-cells.md`. The read site is `generateFoldPath`, `cynefinBoundaries.ts:52-80`.
- charts-59: The fold MUST NOT use the upstream per-point mulberry32 seeds. [just lean-parity]
    Upstream seeds mulberry32 per point (`seed + i * 17`, `seed + i * 31 + 7`). This family uses one xorshift32 stream instead. The shape is the same family, but the random source differs.

## Info

- charts-60: The info text MUST be `"v" + Version`, which is `v0.1.0`. [just lean-parity]
    Upstream writes `v${version}` (read `infoRenderer.ts`).
- charts-61: The info vector canvas MUST be `info.width` by `info.height` (400 by 100 px), with the text centred at `(info.text_x, info.text_y)`, which is (100 px, 40 px), with `text-anchor: middle` at `info.font_size` (32 px). In the cell profile the canvas MUST be one row of the text width, with the text starting at column 0. [just lean-parity]

## Treemap

- charts-62: The treemap canvas MUST be `treemap.width` by `treemap.height` (960 by 500 px; read `renderer.ts:39-41`). [just lean-parity]
    If the `nodeWidth` config is set, the width is `nodeWidth * 10` px; the height works the same way with `nodeHeight`. This upstream quirk is kept.
- charts-63: Treemap children MUST be sorted by value, largest first, with ties going to the declaration index, smallest first. [just lean-parity]
    Upstream uses a stable sort on value (`renderer.ts:145-146`), and the index tie makes the order total. A parent's value is the sum of its leaves.
- charts-64: The treemap insets MUST be `treemap.section_header` 25 px (1600 units), `treemap.section_padding` 10 px (640 units), and `treemap.inner_padding` 10 px (640 units) unless the `padding` config key sets it. [just lean-parity]
    Upstream `renderer.ts` sets these as `SECTION_HEADER_HEIGHT`, `SECTION_INNER_PADDING`, and `DEFAULT_INNER_PADDING`. Cell values: `treemap.section_header` is 2 rows; `treemap.section_padding` is 2 columns and 1 row; `treemap.inner_padding` is 2 columns and 1 row.
    Let `h = floor_div(treemap.inner_padding, 2)`, taken per axis in the cell profile (1 column and 0 rows, so adjacent leaves share a boundary row). The children area of a container is the container inset by `treemap.section_header + treemap.section_padding - h` on top, and by `treemap.section_padding - h` on the left, right, and bottom (read `renderer.ts:151-157`). Each child's squarify cell is then inset by `h` on each side to give its drawn rectangle. A drawn child edge sits `treemap.section_padding` inside its container on the left, right, and bottom, and `treemap.section_header + treemap.section_padding` inside on top.
    This matches d3-hierarchy 3.1.2 `src/treemap/index.js`, `positionNode`, which tiles the area `paddingLeft(node) - paddingInner(node) / 2` inside the node and insets each child by `paddingInner / 2`. The integer rounding is ours.
- charts-65: The treemap squarify ratio MUST be `phi = (1 + sqrt(5)) / 2`, held as `treemap.rho_q30` = 1737350766, which is `floor(phi * 2^30)` and fits the int32 constants table. [just gen-check]
    `tools/specgen` computes it as `floor_div(2^30 + isqrt(5 * 2^60), 2)` in big-integer arithmetic, recomputes it, and fails `gen-check` on a mismatch. The port differs from the float `phi` by less than 2^-30 relative.
- charts-66: The treemap values MUST total at most `2^treemap.value_bits` (2^24), and a larger total MUST normalise each value to `floor_div(v * 2^24, V)`. [just lean-parity]
- charts-67: The squarify test MUST use `alpha = floor_div(Dmax * 2^70, Dmin * V * treemap.rho_q30)` in Q40 (`u128`), where `dx` and `dy` are the free rectangle sides and `Dmax` and `Dmin` the longer and shorter sides. [just lean-parity]
    The `2^70` is `2^30 * 2^40`: `2^30` cancels the scale of `treemap.rho_q30`, and `2^40` sets Q40.
- charts-68: A candidate row with sum `S`, minimum `m`, and maximum `M` MUST have `beta = S^2 * alpha` (Q40) and the row aspect `f = max(floor_div(M * 2^80, beta), floor_div(beta, m))` (Q40). [just lean-parity]
- charts-69: A squarify row MUST start at the first non-zero child, and MUST take these decisions. [just lean-parity]
    Zero-valued children before that child join the row with zero size. Add the next child while `f` does not grow (`f_new <= f_old`). A zero-valued child makes `m = 0`, so `f` is infinite, as in d3 (`beta / 0`); a zero-valued child therefore closes the row and starts the next one. Otherwise, if `f` grows, remove that child and close the row.
- charts-70: A closed row MUST become a strip of thickness `t = round(dy * S / V)` when `dx < dy` (dice), else a column of width `t = round(dx * S / V)`, with `round(x / y) = floor_div(2x + y, 2y)`. [just lean-parity]
    For a dice row, child `k` starts at `x0 + round(dx * cum_k / S)`, where `cum_k` is the prefix sum within the row. For a column, the same rule applies along y. The last boundary is `x0 + dx`.
- charts-71: The squarify free rectangle MUST shrink by `t` on the strip side and `V` MUST drop by `S`; when the remaining `V` is 0, the strip MUST take the rest of the free rectangle. [just lean-parity]
    Children of one container partition its area exactly. Adjacent children share a boundary, and each boundary is rounded once.
- charts-72: The squarify loop MUST recurse on fuel `treemap.squarify_cap` (2000, equal to the node limit). [just lean-parity]
    d3-hierarchy 3.1.2 `src/treemap/squarify.js` (`squarifyRatio`, with `ratio = phi`) adds the next child while `newRatio <= minRatio`; it stops at `if (newRatio > minRatio)`. `round(true)` (`src/treemap/round.js`) applies `Math.round` to each node's `x0`, `y0`, `x1` and `y1` after layout, so each shared boundary is rounded once. For non-negative values, `floor_div(2x + y, 2y)` gives the same result as `Math.round(x / y)`. `renderer.ts:149-158` sets no `tile`.

## Sankey

- charts-73: The sankey canvas MUST be `sankey.width` by `sankey.height`: 600 px / 75 columns by 400 px / 25 rows. In units, `W = 64 * sankey.width` and `H = 64 * sankey.height`. [just lean-parity]
    Both sizes are schema defaults (`config.schema.yaml` lines 2698 to 2703), read as `conf?.width` and `conf?.height` (`sankeyRenderer.ts` lines 90 and 91). The fallback on line 91 reads `defaultSankeyConfig.width` (600), an upstream slip; it is not reached while the schema default for `height` is set.
- charts-74: The sankey node width MUST be `sankey.node_width` (10 px), and the node padding MUST be `sankey.node_padding` (12 px), plus `sankey.show_values_pad` (15 px) when `showValues` is set. In units, `node_w = 64 * nodeWidth` and `pad = 64 * nodePadding`, where `nodePadding` includes the 15 px when `showValues` is set. [just lean-parity]
    The read sites are `sankeyRenderer.ts:99` for the node width, `:100` for the padding, and `:124` for the value padding.
- charts-75: Sankey alignment MUST be `justify` by default, from `nodeAlignment`. [just lean-parity]
    Under justify, a node with no outgoing link goes to the last column. Any other node goes to its depth, which is the longest path from a source. The read sites are `sankeyRenderer.ts:93`, `:116`. d3-sankey 0.12.3 `src/align.js` (`justify`) returns `node.depth` for a node with outgoing links, and `src/sankey.js` (`computeNodeDepths`) propagates depths one link per round from every node, so the last round to reach a node leaves its longest-path depth.
- charts-76: A sankey column x MUST be `x_col = floor_div(col * (W - node_w), maxCol)`, where `maxCol` is the largest depth. [just lean-parity]
    d3-sankey 0.12.3 `src/sankey.js` (`computeNodeLayers`) places column `i` at `x0 + i * kx` with `kx = (W - nodeWidth) / (columns - 1)` and `columns = max depth + 1`. The `maxCol >= 1` guard is ours; d3 divides by zero for a single column.
- charts-77: A sankey node value MUST be `max(sum of incoming, sum of outgoing)`. [just lean-parity]
- charts-78: The sankey positions and relaxation MUST be the integer port of `d3-sankey` 0.12.3 `src/sankey.js` (`computeNodeLayers`, `initializeNodeBreadths`, `computeNodeBreadths`, `relaxRightToLeft`, `relaxLeftToRight`, `resolveCollisions`, `targetTop`, `sourceTop`, `reorderLinks`, `reorderNodeLinks`), read at `https://unpkg.com/d3-sankey@0.12.3/src/sankey.js`, and MUST run exactly these rules, with `pad` the node padding in units, `H` the canvas height in units, and `n` the column count. [just lean-parity]
    d3-sankey runs `iterations` = 6 with `alpha = 0.99^i` and `beta = max(1 - alpha, (i + 1) / iterations)`, and `sankeyRenderer.ts` does not change them. Two rounding choices are this plan's own: each move is rounded half up, and `alpha_i` is the exact floor of `0.99^i` in Q16.
    ```text
    - Padding: py is the gap between two nodes of one column, in units. If the largest column has one node, py = pad. Otherwise py = min(pad, floor_div(H, m - 1)), where m is the largest column node count. py MUST be computed once, before ky.
    - Scale: ky is one Q16 scale for all columns. For a column c with n_c nodes and node value sum S_c > 0, the candidate is floor_div((H - (n_c - 1) * py) * 65536, S_c). ky MUST be the smallest candidate. If no column has S_c > 0, ky = 0. If H - (n_c - 1) * py < 0 for any column, the layout returns domain. Node height is h = floor_div(value * ky, 65536). Link width is w = floor_div(link.value * ky, 65536).
    - Initial positions: each node has layer, its column index. For each column, in list order (declaration order), node k from 0 gets y0 = prefix_k, where prefix_0 = 0 and prefix_(k+1) = prefix_k + h_k + py. Its y1 = y0 + h_k. Let S = h_0 + ... + h_(n_c - 1) and N = H - S - (n_c - 1) * py. N >= 0, because S <= H - (n_c - 1) * py by the choice of ky. Node k MUST then add offset_k = floor_div((k + 1) * N, n_c + 1) to y0 and y1. This is the only division in the initial positions.
    - Initial link order (reorderLinks): after a column gets its positions, each node sorts its sourceLinks by link index. Their targets are in later columns, whose y0 values are not set yet, so the key ties. Each node sorts its targetLinks by (source.y0, link index). The sources are in earlier columns, so their y0 values are final.
    - reorderNodeLinks(v): after node v moves in a pass, for each incoming link l of v, sort l.source.sourceLinks by (link.target.y0, link.index). For each outgoing link l of v, sort l.target.targetLinks by (link.source.y0, link.index). Every link sort uses the link index as its last key. No custom link sort is used.
    - Iterations: sankey.iterations = 6. For i from 0 to sankey.iterations - 1: alpha_i = floor_div(65536 * 99^i, 100^i) (so alpha_0 = 65536; the powers fit int64 for i <= 5) and beta_i = max(65536 - alpha_i, floor_div((i + 1) * 65536, sankey.iterations)). beta_5 = 65536. Iteration i runs the right-to-left pass with (alpha_i, beta_i), then the left-to-right pass with the same pair.
    - Right-to-left pass: for c from n - 2 down to 0, take each node s of column c in list order.
      - Set Y to the sum of sourceTop(s, t) * v, and W to the sum of v, over s.sourceLinks in list order. Here t is the link target and v = link.value * (t.layer - s.layer).
      - If W <= 0, skip s. Otherwise set dy = round_half_up((round_half_up(Y, W) - s.y0) * alpha, 65536), add dy to s.y0 and s.y1, then run reorderNodeLinks(s).
      - After all nodes of column c move, sort the column list by y0 (see Stable sort). Then run resolveCollisions(list, beta).
    - Left-to-right pass: for c from 1 to n - 1, take each node t of column c in list order. Use the same steps, with Y the sum of targetTop(s, t) * v and W the sum of v over t.targetLinks. Here s is the link source and v = link.value * (t.layer - s.layer). The move adds dy to t.y0 and t.y1.
    - targetTop and sourceTop in integers. Each returns floor_div(N, 2) for the integer N below.
      - targetTop(s, t): N = 2 * s.y0 - (c_s - 1) * py + 2 * A - 2 * B. Here c_s is the length of s.sourceLinks. A is the sum of (link.width + py) over the links of s.sourceLinks before the first link whose target is t. B is the sum of link.width over the links of t.targetLinks before the first link whose source is s.
      - sourceTop(s, t): N = 2 * t.y0 - (c_t - 1) * py + 2 * A' - 2 * B'. Here c_t is the length of t.targetLinks. A' is the sum of (link.width + py) over the links of t.targetLinks before the first link whose source is s. B' is the sum of link.width over the links of s.sourceLinks before the first link whose target is t.
    - Stable sort: a column list sorts by y0 only, with JavaScript Array.prototype.sort. That sort is stable (ECMA-262, since ES2019), so equal y0 values keep their list order. The declaration index is not a sort key here.
    - resolveCollisions(list, beta): let m be the list length, k = floor_div(m, 2), and subj = list[k]. The four sweeps MUST run in this order:
      1. BottomToTop(list, subj.y0 - py, k - 1, beta).
      2. TopToBottom(list, subj.y1 + py, k + 1, beta).
      3. BottomToTop(list, H, m - 1, beta).
      4. TopToBottom(list, 0, 0, beta).
      Sweep 1 does not move subj, so sweep 2 reads the same subj.y1.
      - TopToBottom(list, y, i, beta): for j from i up to m - 1, set dy = round_half_up((y - list[j].y0) * beta, 65536). If dy > 0, add dy to list[j].y0 and list[j].y1. Then set y = list[j].y1 + py.
      - BottomToTop(list, y, i, beta): for j from i down to 0, set dy = round_half_up((list[j].y1 - y) * beta, 65536). If dy > 0, subtract dy from list[j].y0 and list[j].y1. Then set y = list[j].y0 - py.
      - A sweep with no index in range does nothing. Each product with beta is checked for int64 overflow.
    - Link ends: after the last iteration, for each node and each outgoing link l, l.y0 = node.y0 + (sum of the widths of the links before l in sourceLinks) + floor_div(l.width, 2). For each incoming link l, l.y1 = node.y0 + (sum of the widths of the links before l in targetLinks) + floor_div(l.width, 2).
    ```
- charts-79: A sankey link MUST be drawn in the vector profile as `M x_s,y_s C xm,y_s xm,y_t x_t,y_t`, a cubic Bezier from the source right edge `x_s` at the link's source `y0` to the target left edge `x_t` at the link's target `y1`, with `xm = floor_div(x_s + x_t, 2)`. The cell profile MUST draw it as braille. [just lean-parity]
    d3-sankey 0.12.3 `sankeyLinkHorizontal` calls `linkHorizontal` from its own d3-shape 1.3.7 (`src/link/index.js`, `curveHorizontal`), which gives this path.
- charts-80: After the last iteration (`beta = 65536`), the nodes of each column MUST be disjoint and each gap MUST be at least `py`. [just lean-parity]
    A collision pass with `beta < 65536` moves only part of an overlap, so it does not give disjointness.

## Pie

- charts-81: The pie height `pie.height` MUST be 450 px, the pie width MUST equal the height, the centre MUST be `(pieW / 2, H / 2)`, and the radius MUST be `min(pieW, H) / 2 - pie.margin`, which is 185 px in the vector profile. [just lean-parity]
    The read site is `pieRenderer.ts:41-56`.
- charts-82: The donut inner radius MUST be `floor_div(radius * donutHole_m, 1000)` when `0 < donutHole <= 0.9`, and 0 otherwise, and the label radius MUST be `floor_div(radius * textPosition_m, 1000)`. [just lean-parity]
    The read sites are `pieRenderer.ts:53-55` and `:64`. The `textPosition` default is 0.75, which is 750 thousandths (`PieDiagramConfig`).
- charts-83: Pie slices MUST keep declaration order, with no sort, and a total `T` of 0 MUST draw no slices. [just lean-parity]
    The read site is `pieRenderer.ts:21` (`.sort(null)`). The total is the sum of the values in thousandths.
- charts-84: The pie angle allocation MUST follow these rules. [just lean-parity]
    For each slice, `num_k = v_k * 65536`, `b_k = floor_div(num_k, T)`, and `rem_k = num_k mod T`. Let `R = 65536 - sum of b_k`, which satisfies `0 <= R < n`. The `R` slices with the largest `rem_k` each get one extra unit. Ties go to the declaration index, smallest first. The slices then sum to exactly 65536. Boundaries are cumulative from 0.
    The Lean rules are `base_i = Int.fdiv (65536 * v_i) T`, `frac_i = Int.fmod (65536 * v_i) T`, `T = sum v_i > 0`, and `r = 65536 - sum base_i`.
- charts-85: A pie slice with start angle `start` and sweep `s` MUST be one `Path`, with `a0 = start - 16384` in the angle convention of the Arc rule of `spec/render-cells.md`. [just lean-parity]
    With `innerRadius` = 0 the commands are `M cx cy`, `L` to vertex 0 of the outer arc, `A cx cy r a0 s`, and `Z`. With `innerRadius` > 0 the commands are `M` at vertex 0 of the outer arc, `A cx cy r a0 s`, `L` to the first vertex of the inner arc, `A cx cy innerRadius (a0 + s) (-s)`, and `Z`, so the inner arc runs from the end angle back to the start angle, as d3-shape 3.2.0 `src/arc.js` does (`context.arc(0, 0, r0, a10, a00, cw)`). A zero sweep draws nothing. The Arc rule is the only arc flattening; this kind adds none. The large-arc flag is `angle > 32768`. The endpoints are `x = cx + Int.fdiv (R * sin_q15 a) 32768` and `y = cy - Int.fdiv (R * cos_q15 a) 32768`.
- charts-86: A pie label MUST sit at angle `start + floor_div(s, 2)` on the label radius, with a middle anchor, and the legend row pitch MUST be `pie.legend_row` (22 px). [just lean-parity]
    The row pitch is 18 + 4; the read sites are `pieRenderer.ts:39-40` and `:192`.

## Radar

- charts-87: The radar radius MUST be `R = min(W, H) / 2`, with `radar.width` equal to 600 px / 75 columns and `radar.height` equal to 600 px / 38 rows, so `R` is 300 px at the defaults. [just lean-parity]
    Both are schema defaults (`config.schema.yaml` lines 2909 to 2918), read as `config.width` and `config.height` (`radar/renderer.ts` line 26). The chart does not size itself from its container.
- charts-88: Axis `j` of `n` axes MUST have `theta_j = floor_mod(floor_div(j * 65536, n) - 16384, 65536)`, and a point at radius `r` MUST be `x = floor_div(r * cos_q15(theta), 32768)` and `y = floor_div(r * sin_q15(theta), 32768)`. [just lean-parity]
    Upstream uses `2 pi j / n - pi / 2` (read `renderer.ts:84`, `:105`, `:154`).
- charts-89: A radar value radius MUST be `clip = min(max(v, min), max)` and `r = floor_div(R * (clip - min), max - min)`, and `max <= min` MUST emit `radar/empty-range` (error) and draw no curve. [just lean-parity]
    The read site is `relativeRadius`, `renderer.ts:175-183`.
- charts-90: The radar tick count MUST default to `radar.ticks_default` (5), and a value above `radar.ticks_max` (32) MUST clamp to 32. [just lean-parity]
    The read site is `db.ts:111-115`.
- charts-91: Graticule circle `i` MUST have radius `floor_div(R * (i + 1), ticks)`, and the polygon graticule MUST use the same radii with vertices at `theta_j`. [just lean-parity]
- charts-92: The radar legend MUST be `legendX = floor_div((W / 2 + marginRight) * 3, 4)`, `legendY = floor_div(-(H / 2 + marginTop) * 3, 4)`, with pitch `radar.legend_row` (20 px). [just lean-parity]
    `marginRight` and `marginTop` default to `radar.margin`, which is 50 px, or 3200 units (`radar` config). `drawLegend` in `radar/renderer.ts:220-221` reads them.
- charts-93: A radar axis label MUST sit at radius `R + radar.label_gap` on the axis angle, with `radar.label_gap` equal to 19 px / 3 columns and 2 rows. [just lean-parity]
    Upstream puts the label at `R * axisLabelFactor + 4 px` (`radar/renderer.ts` lines 123 to 130; `axisLabelFactor` default 1.05, `config.schema.yaml` line 2948). At `R = 300 px` that is `R + 19 px`. The constant does not scale with `R`.
- charts-94: A radar curve in the vector profile MUST be a closed Catmull-Rom curve with tension `t_m` in thousandths, equal to `radar.curve_tension` (170). [just lean-parity]
    `t_m` comes from the config key `radar.curveTension` (default 0.17, `config.schema.yaml` lines 2949 to 2954, times 1000). For point `i` with `p0 = p_{i-1}`, `p1 = p_i`, `p2 = p_{i+1}`, and `p3 = p_{i+2}` (indices mod `n`), `cp1 = p1 + floor_div((p2 - p0) * t_m, 1000)` and `cp2 = p2 - floor_div((p3 - p1) * t_m, 1000)` (read `closedRoundCurve`, `renderer.ts:186-204`). In the cell profile the curve is braille.

## Venn

- charts-95: The venn layout MUST NOT port `@upsetjs/venn.js`, and it MUST enforce these set counts. [just lean-parity]
    Zero sets emit `venn/no-sets` (error). One set is one circle at the canvas centre. Two and three sets follow the rules below. More than three sets emit `venn/too-many-sets` (error). Upstream computes this layout with `@upsetjs/venn.js` (read `vennRenderer.ts:11`).
- charts-96: The venn canvas MUST be `4R` by `4R`, where `R = venn.max_radius`, with the centre at `(2R, 2R)`. [just lean-parity]
    `venn.max_radius` is 112 px / 14 columns and 7 rows, which is `floor_div(min(venn.width, venn.height), 4)` with the schema defaults 800 and 450 (`config.schema.yaml` lines 3083 to 3092). Upstream reads `config.width` and `config.height` (`venn/vennRenderer.ts` lines 64 and 65). The canvas is 448 px, or 56 by 28 cells.
- charts-97: Every venn set radius MUST be `r_i = isqrt(floor_div(R^2 * s_i, s_max))`, computed in `u128`, where `s_max` is the largest size, which is non-zero. [just lean-parity]
- charts-98: A two-set venn MUST use the target `T = floor_div(R^2 * o, s_max)`, a lens area divided by pi, where `o` is the overlap and 0 when absent. [just lean-parity]
- charts-99: `G(d)`, scaled by 2^32, MUST be the pi-free lens area at centre distance `d >= 1`, computed as follows. [just lean-parity]
    For each circle `i`, with `j` the other circle: `x_i = clamp(floor_div((d^2 + r_i^2 - r_j^2) * 32768, 2 * d * r_i), -32768, 32768)`, which is Q15; `u_i = arccos_turns(x_i)`; `F_i = 131072 * u_i - 20861 * sin_q15(2 * u_i)`; and `G(d) = sum of r_i^2 * F_i` (`u128`).
    `F_i` equals `2^32 * (alpha_i - sin(alpha_i) cos(alpha_i)) / pi`, where `alpha_i = 2 pi u_i / 65536`. The constant 20861 is `65536 / pi`, rounded.
- charts-100: `arccos_turns(x)` MUST return the largest `u` in `[0, 32768]` with `cos_q15(u) >= x`, by a binary search over `[0, 32768]` with exactly `venn.acos_iterations` (16) steps. [just lean-parity]
    Each step is `mid = floor_div(lo + hi + 1, 2)`. If `cos_q15(mid) >= x`, set `lo = mid`; otherwise set `hi = mid - 1`.
- charts-101: The two-set bisection MUST use `lo = |r1 - r2|` and `hi = r1 + r2`, and MUST apply these special cases in order. [just lean-parity]
    1. If `T >= min(r1, r2)^2`, the smaller circle lies inside the lens; use `d = lo`.
    2. If `T = 0`, use `d = hi`.
    3. `G(0)` is defined as `min(r1, r2)^2 * 2^32`.
- charts-102: The two-set bisection MUST run exactly `venn.bisect_iterations` (32) steps of `mid = floor_div(lo + hi, 2)`, setting `lo = mid` when `G(mid) > T * 2^32` and `hi = mid` otherwise, and MUST return `d = floor_div(lo + hi, 2)`. [just lean-parity]
- charts-103: The two-set placement MUST be `A = (2R - floor_div(d, 2), 2R)` and `B = (A.x + d, 2R)`. [just lean-parity]
- charts-104: A three-set venn MUST use the fixed symmetric arrangement `A = (2R, R)`, `B = (2R + floor_div(R * venn.sqrt3_half_q15, 32768), 2R + floor_div(R, 2))`, and `C = (2R - floor_div(R * venn.sqrt3_half_q15, 32768), 2R + floor_div(R, 2))`, with `venn.sqrt3_half_q15` equal to 28378, which is `round(sqrt(3)/2 * 32768)`. [just lean-parity]
    The overlaps are not matched in this arrangement. Only the set sizes set the radii.
- charts-105: A venn region label anchor MUST be the integer mean of the member centres, with `floor_div` per coordinate. [just lean-parity]
    The anchor is not guaranteed to lie inside an exclusive region. This is ours.
- charts-106: All venn geometry MUST be in dots in the cell profile. [just lean-parity]

## Proofs

- charts-107: The shared scale theorems in `proofs/Elegant/Chart/Scale.lean` MUST hold. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`linear_monotone`|`plo <= phi -> v <= v' -> linear v <= linear v'`|numerator is monotone; `Int.fdiv` is monotone in the numerator for a positive divisor|
    |`linear_antitone`|`phi <= plo -> v <= v' -> linear v' <= linear v`|as `linear_monotone` with the sign flipped|
    |`linear_into_plot`|`dlo <= v <= dhi -> min plo phi <= linear v <= max plo phi`|bounds on the numerator, then floor bounds|
    |`band_disjoint`|`i < j -> bandEnd i <= bandStart j` with `bandEnd = bandStart` (bandwidth 0)|`bandStart k = floor_div(k * R, n - 1)` for `n >= 2`; induction on `j`; `bandStart` grows by at least 1 per index when `R >= n - 1`, because `floor(a + b) >= floor(a) + floor(b)`; `omega`|
    |`ticks_scan_fuel_sufficient`|`C <= D < 2^31 -> exists e, 0 <= e <= 9 and 10^e * C <= D < 10^(e+1) * C`|invariant of the fuel-bounded scan with fuel `chart.scan_cap`; `decide` over the powers of ten up to `10^9`|
    |`ticks_step_is_125`|the chosen step is `p * m` with `p = 10^e` and `m` in `{1, 2, 5}` (the `m = 10` case is `1` at `e + 1`)|`decide` over the four candidates; `omega`|
    |`ticks_inside_domain`|every tick `t` satisfies `dlo <= t <= dhi`|floor bounds with `step > 0`|
    |`ticks_count_le`|the tick count is `<= 2 * c + 1`|`D / step <= 2 * C` because the step is chosen by the squared thresholds; floor bounds|
- charts-108: The Gantt theorems in `proofs/Elegant/Chart/Gantt.lean` MUST hold. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`gantt_civil_roundtrip`|`civilFromDays (daysFromCivil y m d) = (y, m, d)` for each valid proleptic Gregorian date|Hinnant era decomposition with `Int.fdiv`; `omega` on each month branch|
    |`gantt_day_order`|`(y, m, d) < (y', m', d')` in lexicographic order implies `daysFromCivil y m d < daysFromCivil y' m' d'`|the same decomposition; `omega` per case|
    |`gantt_axis_monotone`|`d <= d' -> x d <= x d'` on the time axis|`linear_monotone`|
    |`gantt_task_rows_disjoint`|task rows `i < j` have `rowEnd i <= rowStart j`|`band_disjoint`|
    |`gantt_bars_inside_axis`|each bar rect lies inside the plot, with the axis domain `[min start, max end]`|`linear_into_plot` on the start and end dates|
    |`gantt_valid`|`WellFormed m -> WithinLimits m -> Gantt.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-109: The xychart theorems in `proofs/Elegant/Chart/XY.lean` MUST hold. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`xychart_bar_inside_plot`|each bar rect lies inside the plot rect|`band_disjoint` and `linear_into_plot`|
    |`xychart_points_inside_plot`|each line point lies inside the plot rect|`linear_into_plot` on both axes|
    |`xychart_valid`|`WellFormed m -> WithinLimits m -> XYChart.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-110: The quadrant theorems in `proofs/Elegant/Chart/Quadrant.lean` MUST hold. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`quadrant_point_in_plot`|after clamping to `[0, 1000]`, each point lies inside the plot rect|`linear_into_plot` on both axes|
    |`quadrant_split_monotone`|`x >= 500 -> px >= centre_x`|`linear_monotone` at the midpoint of the domain|
    |`quadrant_valid`|`WellFormed m -> WithinLimits m -> Quadrant.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-111: The treemap theorems in `proofs/Elegant/Chart/Treemap.lean` MUST hold. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`treemap_children_sorted`|the children of each parent are `List.mergeSort` of the children by key (value descending, then declaration index ascending)|`List.pairwise_mergeSort`; `List.mergeSort_perm`|
    |`treemap_squarify_fuel`|the squarify loop places each child exactly once within `treemap.squarify_cap` iterations|fuel-bounded loop; invariant: remaining children <= remaining fuel|
    |`treemap_children_disjoint`|the child rects of one parent are pairwise `Disjoint`|induction on the strips; each strip is a band (`placeAfter_disjoint`); children inside a strip are stacked (`compact_pairwise_disjoint`)|
    |`treemap_children_inside_parent`|`contains parent child.rect` for each child|induction on the strips; `omega`|
    |`treemap_area_exact`|`sum over children of (w * h) = W * H` for the parent `W x H`|induction on the strips; invariant: the remaining rectangle is the parent minus the placed strips; each boundary is `x0 + round(dx * cum_k / S)` and the last boundary is `x0 + dx`, so the widths telescope to the strip width; `omega`|
    |`treemap_valid`|`WellFormed m -> WithinLimits m -> Treemap.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-112: The Wardley theorems in `proofs/Elegant/Chart/Wardley.lean` MUST hold. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`wardley_points_in_plot`|after clamping to `[0, 100000]` on both axes, each component lies inside the plot rect|`linear_into_plot`|
    |`wardley_links_join_nodes`|each link starts and ends at the centres of its two nodes|definitional|
    |`wardley_valid`|`WellFormed m -> WithinLimits m -> Wardley.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-113: The pie theorems in `proofs/Elegant/Chart/Pie.lean` MUST hold, over the rules `base_i = Int.fdiv (65536 * v_i) T`, `frac_i = Int.fmod (65536 * v_i) T`, `T = sum v_i > 0`, `r = 65536 - sum base_i`, the extra unit for the `r` slices with the largest `frac_i` (ties by declaration index), slices starting at angle 0 and running clockwise in declaration order, and the endpoints `x = cx + Int.fdiv (R * sin_q15 a) 32768` and `y = cy - Int.fdiv (R * cos_q15 a) 32768`. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`pie_remainder_lt_count`|`0 <= r < n`|`sum frac_i = r * T` and each `frac_i < T`; `omega`|
    |`pie_angles_sum_turn`|`sum angle_i = 65536` exactly|`65536 * T = sum (base_i * T + frac_i)`, so the extra units close the sum|
    |`pie_extra_only_positive_frac`|a slice with `frac = 0` receives no extra unit|counting argument: `sum frac_i = r * T` with `frac_i < T` forces more than `r` positive fractions|
    |`pie_slices_contiguous`|`start_0 = 0`, `start_(i+1) = start_i + angle_i`, and the last end is `65536`; declaration order is kept|induction on the slice list|
    |`pie_endpoints_in_square`|`abs (x - cx) <= R` and `abs (y - cy) <= R` for each endpoint|`decide` over the 1025-entry sine table gives `abs (sin_q15 a) <= 32768`; floor bounds|
    |`pie_valid`|`WellFormed m -> WithinLimits m -> Pie.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-114: The radar theorems in `proofs/Elegant/Chart/Radar.lean` MUST hold, over the axis angle `a_i = floor_mod(Int.fdiv (65536 * i) n - 16384, 65536)`, the radius `r = Int.fdiv (R * (clip - min)) (max - min)` with `clip = min(max(v, min), max)`, and the point `(cx + Int.fdiv (r * cos_q15 a_i) 32768, cy + Int.fdiv (r * sin_q15 a_i) 32768)` in the square of half side `R` centred on `(cx, cy)`. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`radar_axis_angles_distinct`|`i < j < n <= 65536 -> a_i != a_j`|the unshifted angles differ by at least 1 because `65536 / n >= 1`; the shift by 16384 is a bijection mod 65536|
    |`radar_radius_bounded`|`0 <= r <= R`|`clamp` bounds|
    |`radar_points_in_plot`|each point lies in the square of half side `R`|`radar_radius_bounded`, `abs (sin_q15) <= 32768` (table check), floor bounds|
    |`radar_valid`|`WellFormed m -> WithinLimits m -> Radar.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-115: The sankey theorems in `proofs/Elegant/Chart/Sankey.lean` MUST hold, over these rules: each product with a Q16 factor is divided once by 65536 with `round_half_up`; each weighted mean is one `round_half_up` by its weight sum; a column sorts by `y0` only, with a stable sort, so equal `y0` values keep the list order; the layout runs `d3-sankey` justify alignment and `sankey.iterations` (6) iterations; each column pass ends with `resolveCollisions`, not with the kernel `compact` sweep; `py` is the padding of the sankey rules. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`sankey_passes_exact`|the relaxation runs exactly `sankey.iterations` passes|fuel-bounded loop; the fuel is the pass count|
    |`sankey_column_gaps_final`|after the last iteration, the nodes of each column are `List.Pairwise Disjoint`, and each gap between consecutive nodes of the column list is `>= py`|a column that no pass touches keeps its initial positions, whose gaps are `py` plus a nonnegative offset difference. Every other column ends with `resolveCollisions` at `beta = 65536`, whose last sweep runs top to bottom from `y = 0`: induction on the list index, since a push at `beta = 65536` moves `y0` by exactly the overlap and no move happens otherwise|
    |`sankey_link_sum_le_height`|for each node, the incoming and the outgoing link widths each sum to at most `node.h`, and the node heights of one column sum to at most `H - (n - 1) * py`|`sum floor_div(v_i * k, 65536) <= floor_div(sum v_i * k, 65536) <= floor_div(value * k, 65536)`, since `sum v_i <= value = max(in, out)`, with `k = ky`, where `ky <= floor_div((H - (n - 1) * py) * 65536, column sum)` for each column, so `floor_div(column sum * k, 65536) <= H - (n - 1) * py`|
    |`sankey_valid`|`WellFormed m -> WithinLimits m -> Sankey.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-116: The venn theorems in `proofs/Elegant/Chart/Venn.lean` MUST hold, over the radii `r_i = isqrt(floor_div(R^2 * s_i, s_max))` with `R = venn.max_radius`, the two-set target `T = floor_div(R^2 * o, s_max)`, `G(d)` built from `arccos_turns` (`venn.acos_iterations` steps) and `F_i = 131072 * u_i - 20861 * sin_q15(2 * u_i)`, the bracket `lo = abs (r1 - r2)` and `hi = r1 + r2`, the three special cases, the predicate `g d = (G(d) > T * 2^32)`, the bisection with `mid = floor_div(lo + hi, 2)`, fuel `venn.bisect_iterations` (32), and `d = floor_div(lo + hi, 2)`. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`venn_bisect_invariant`|after each step, `g lo` and `not (g hi)` hold|invariant of the fuel-bounded loop; case split on `g mid`; holds for any integer `G`, with no monotonicity needed|
    |`venn_bisect_width`|with `hi - lo < 2^32` at the start, after `venn.bisect_iterations = 32` steps `hi - lo <= 1`|width after a step is `<= ceil (w / 2)`; induction on the step count|
    |`venn_bisect_result_in_bracket`|the returned distance lies in `[lo, hi]` and is adjacent to a sign change of `g`|follows from `venn_bisect_invariant` and `venn_bisect_width`|
    |`venn3_inside_canvas`|each of the three circle boxes lies inside the canvas `[0, 4R] x [0, 4R]`|`Rect.bbox_contains`|
    |`venn_too_many_sets`|`n > 3` returns the error `venn/too-many-sets`, `n = 0` returns `venn/no-sets`, and neither returns a scene|case split on `n`|
    |`venn_valid`|`WellFormed m -> WithinLimits m -> Venn.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-117: The cynefin theorems in `proofs/Elegant/Chart/Cynefin.lean` MUST hold, over the frame split at its integer midlines into four fixed domain rects, the xorshift32 generator seeded with `cynefin.seed` when non-zero and `cynefin.default_seed` otherwise, its 15 draws (8 jitters, then 7 segment offsets), and the point rule `x_i = cx + floor_div(u_i * 2A, 2^32) - A`. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`cynefin_domains_tile_frame`|the four domain rects are pairwise `Disjoint`, and their areas sum to the frame area|integer midlines; `omega`|
    |`xorshift32_step_nonzero`|`s != 0 -> step s != 0`|each shift-xor map `x ^ (x << k)` and `x ^ (x >> k)` is injective on 32-bit words (triangular bit matrix), so `step` is injective with `step 0 = 0`|
    |`cynefin_boundary_inside_frame`|each boundary point satisfies `cx - A <= x_i < cx + A` and `0 <= y_i <= H`|`floor_div` bounds with `u_i` in `[0, 2^32)`; `omega`|
    |`cynefin_draw_count`|the generator draws exactly 15 values per diagram|structural recursion on the draw count|
    |`cynefin_valid`|`WellFormed m -> WithinLimits m -> Cynefin.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-118: The info theorems in `proofs/Elegant/Chart/Info.lean` MUST hold. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`info_lines_in_canvas`|each text line rect lies inside the canvas, which is the bounding box of the lines|`Rect.bbox_contains`|
    |`info_valid`|`WellFormed m -> WithinLimits m -> Info.layout m = .ok s -> HardConstraints s`|combines the rows above|
- charts-119: Every chart kind MUST have exactly one validity theorem of the form `WellFormed m -> WithinLimits m -> <Module>.layout m = .ok s -> HardConstraints s`, and it MUST hold. [just proofs]
    The eleven theorems are `gantt_valid`, `xychart_valid`, `quadrant_valid`, `treemap_valid`, `wardley_valid`, `pie_valid`, `radar_valid`, `sankey_valid`, `venn_valid`, `cynefin_valid`, and `info_valid`. Each combines the rows of its own table with the Scale rows where the kind uses a scale.
- charts-120: Every chart constant named in this file MUST be a key of `spec/data/layout-constants.json`, including `chart.number_scale`, `chart.range_units_max`, `chart.tick_count`, `chart.tick_cap`, and the fuel values of this list. [just gen-check]
    The tick scan recurses on `chart.scan_cap` (40: the exponents 0 to 19). The treemap squarify loop recurses on `treemap.squarify_cap` (2000, equal to the node limit). The sankey relaxation recurses on `sankey.iterations` (6). The venn bisection recurses on `venn.bisect_iterations` (32). The cynefin waviness draws 15 values per diagram. Gantt, quadrant, wardley, pie, radar, xychart, and info have no fuel loop.
- charts-121: The chart family MUST NOT claim more than these theorems prove. [just proofs]
    No theorem claims optimal aspect ratio, optimal packing, or a best tick count. Closeness of sankey and treemap geometry to `d3-sankey` and `d3-hierarchy` is checked by the `d3-check` gate, not proven. Closeness of tick steps to the real-number `d3` rule is checked by `d3-check`, not proven. Pie and radar closeness to real trigonometry is not claimed beyond the sine table bound.
- charts-122: Sankey MUST NOT claim these properties. [just proofs]
    No monotone measure decreases during relaxation, no exact flow conservation holds under rounding, and no closeness to `d3-sankey` is proven. The integer port is not proven to equal the floating-point values of `d3-sankey`, and no theorem bounds the difference in units. The `d3-check` gate checks closeness within 1 px (64 units).
- charts-123: Venn MUST NOT claim these properties. [just proofs]
    Nothing claims that the returned distance equals the real-number root of the lens equation, that the root is unique, or that the integer `G(d)` approximates the real lens area. `G(d)` is not part of any theorem above.
- charts-124: The chart module MUST consist of `proofs/Elegant/Chart/Scale.lean` (the shared linear scale, band scale, tick rule, and civil dates) and one module per kind: `Gantt.lean`, `XY.lean`, `Quadrant.lean`, `Treemap.lean`, `Wardley.lean`, `Pie.lean`, `Radar.lean`, `Sankey.lean`, `Venn.lean`, `Cynefin.lean`, and `Info.lean`. [just proofs]
    The `xychart` packet builds the family module first and `Scale.lean` with it; the other chart kinds follow. The braille raster of `spec/render-cells.md` is built before the kinds that draw sloped lines; this family adds no braille code.

## Gates

- charts-125: Sankey and treemap geometry MUST stay within 1 px of `d3-sankey` and `d3-hierarchy`, which is 64 units per coordinate. [just d3-check]
    `tools/upstream-oracle/d3.mjs` runs the two pinned packages on each sankey and treemap fixture and prints every node and rectangle coordinate. The gate compares these with `bin/emd-go layout --profile vector`.
    A fixture whose two sort keys differ by at most one unit in the integer port and tie or swap in `d3` is a discrete order flip. Such a fixture MUST be listed, with its path and the two keys, in `corpus/d3-check-exceptions.txt`; the gate skips each listed fixture and prints the count. Any other `d3-check` failure is a defect in the port and MUST be fixed.
- charts-126: Every series index that a chart scene uses MUST have at least one `Text` whose content is that series' label, on the element, beside it, or in the legend. [just go-check: TestSeriesLabels]
    Rust test `series_labels`. The test runs every corpus fixture of the kinds that have a series index. A fixture with an unlabelled series fails the test.
