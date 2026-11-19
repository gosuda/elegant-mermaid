import Elegant.Kinds.FlowchartIcons

set_option autoImplicit false

namespace Elegant.Grid.Architecture

-- Source coordinates are hundredths of the native 80-unit icon viewport.
def iconScale (v : Int) : Int := Int.fdiv (2 * v * 1536 + 8000) 16000

def iconPoint (origin : Point) (x y : Int) : Point :=
  ⟨origin.x + iconScale x, origin.y + iconScale y⟩

def iconLine (origin : Point) (x y x' y' : Int) : Primitive :=
  .polyline [iconPoint origin x y, iconPoint origin x' y'] 0
    {style := "ink-line",width := .emphasis}

def iconEllipse (origin : Point) (x y rx ry : Int) (fill : Bool := false) : Primitive :=
  .ellipse (origin.x+iconScale x) (origin.y+iconScale y) (iconScale rx) (iconScale ry)
    {style := if fill then "ink" else "ink-line",width := .emphasis}

def iconRect (origin : Point) (x y w h radius : Int) : Primitive :=
  .roundRect ⟨origin.x+iconScale x,origin.y+iconScale y,iconScale w,iconScale h⟩
    (iconScale radius) {style := "ink-line",width := .emphasis}

def rim (origin : Point) (y : Int) : Primitive :=
  .path [.M (iconPoint origin 2000 y),
    .C (iconPoint origin 2000 (y+394)) (iconPoint origin 2895 (y+714)) (iconPoint origin 4000 (y+714)),
    .C (iconPoint origin 5105 (y+714)) (iconPoint origin 6000 (y+394)) (iconPoint origin 6000 y)]
    {style := "ink-line",width := .emphasis}

def serverRow (origin : Point) (y : Int) : List Primitive :=
  let commands := [.M (iconPoint origin 5625 y),
    .C (iconPoint origin 5625 (y+27)) (iconPoint origin 5580 (y+50)) (iconPoint origin 5525 (y+50)),
    .L (iconPoint origin 4475 (y+50)),
    .C (iconPoint origin 4420 (y+50)) (iconPoint origin 4375 (y+27)) (iconPoint origin 4375 y),
    .C (iconPoint origin 4375 (y-27)) (iconPoint origin 4420 (y-50)) (iconPoint origin 4475 (y-50)),
    .L (iconPoint origin 5525 (y-50)),
    .C (iconPoint origin 5580 (y-50)) (iconPoint origin 5625 (y-27)) (iconPoint origin 5625 y), .Z]
  [.path commands {style := "ink"}, .path commands {style := "ink-line",width := .emphasis},
    iconEllipse origin 3250 y 75 75 true,iconEllipse origin 2750 y 75 75 true,
    iconEllipse origin 2250 y 75 75 true]

def knownIcon (name : String) : Bool :=
  ["cloud","database","disk","internet","server"].contains name

def iconItems (profile : Profile) (name : String) (origin : Point) : List Primitive :=
  if profile == .cell then
    [.symbolRef (if knownIcon name then name else "unknown") origin
      (if knownIcon name then "ink-line" else "ink")]
  else match name with
  | "database" => [rim origin 5786,rim origin 4595,rim origin 3405,
      iconEllipse origin 4000 2214 2000 714,iconLine origin 2000 5786 2000 2214,
      iconLine origin 6000 5786 6000 2214]
  | "server" => [iconRect origin 1750 1750 4500 4500 200,
      iconLine origin 1750 3250 6250 3250,iconLine origin 1750 4750 6250 4750] ++
      serverRow origin 2500 ++ serverRow origin 4000 ++ serverRow origin 5500
  | "disk" => [iconRect origin 2000 1500 4000 5000 100,
      iconEllipse origin 2400 1917 80 83,iconEllipse origin 5600 1917 80 83,
      iconEllipse origin 2400 6083 80 83,iconEllipse origin 5600 6083 80 83,
      iconEllipse origin 4000 3375 1400 1458,iconEllipse origin 4000 3375 400 417 true,
      iconEllipse origin 4000 3375 400 417,
      .path [.M (iconPoint origin 3751 4252),.L (iconPoint origin 3268 5574),
        .C (iconPoint origin 3242 5645) (iconPoint origin 3158 5676) (iconPoint origin 3092 5638),
        .L (iconPoint origin 2674 5396),
        .C (iconPoint origin 2608 5358) (iconPoint origin 2593 5270) (iconPoint origin 2641 5212),
        .L (iconPoint origin 3542 4132),
        .C (iconPoint origin 3630 4027) (iconPoint origin 3798 4124) (iconPoint origin 3751 4252),.Z]
        {style := "ink"}]
  | "cloud" => [.path [.M (iconPoint origin 6500 4750),
      .C (iconPoint origin 6500 5026) (iconPoint origin 6276 5250) (iconPoint origin 6000 5250),
      .L (iconPoint origin 2000 5250),
      .C (iconPoint origin 1724 5250) (iconPoint origin 1500 5026) (iconPoint origin 1500 4750),
      .C (iconPoint origin 1500 4563) (iconPoint origin 1603 4399) (iconPoint origin 1756 4314),
      .C (iconPoint origin 1752 4293) (iconPoint origin 1750 4272) (iconPoint origin 1750 4250),
      .C (iconPoint origin 1750 3990) (iconPoint origin 1998 3776) (iconPoint origin 2315 3753),
      .C (iconPoint origin 2480 3302) (iconPoint origin 2949 2977) (iconPoint origin 3500 2977),
      .C (iconPoint origin 3586 2977) (iconPoint origin 3669 2985) (iconPoint origin 3750 3000),
      .C (iconPoint origin 3959 2843) (iconPoint origin 4219 2750) (iconPoint origin 4500 2750),
      .C (iconPoint origin 5110 2750) (iconPoint origin 5619 3188) (iconPoint origin 5728 3767),
      .C (iconPoint origin 5942 3823) (iconPoint origin 6100 4018) (iconPoint origin 6100 4250),
      .C (iconPoint origin 6100 4253) (iconPoint origin 6100 4257) (iconPoint origin 6099 4260),
      .C (iconPoint origin 6328 4306) (iconPoint origin 6500 4508) (iconPoint origin 6500 4750),.Z]
      {style := "ink-line",width := .emphasis}]
  | "internet" => [iconEllipse origin 4000 4000 2250 2250,
      iconLine origin 4000 1750 4000 6250,iconLine origin 1750 4000 6250 4000,
      .path [.M (iconPoint origin 3999 1751),
        .C (iconPoint origin 2471 2861) (iconPoint origin 2471 5139) (iconPoint origin 3999 6249)]
        {style := "ink-line",width := .emphasis},
      .path [.M (iconPoint origin 4001 1751),
        .C (iconPoint origin 5529 2861) (iconPoint origin 5529 5139) (iconPoint origin 4001 6249)]
        {style := "ink-line",width := .emphasis},
      iconLine origin 1975 3010 6025 3010,iconLine origin 1975 4990 6025 4990]
  | _ => [Kinds.Flowchart.unknownGlyphPath origin]

end Elegant.Grid.Architecture
