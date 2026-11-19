import Elegant.Chart.Treemap
import Elegant.Chart.XY

namespace Elegant.Treemap

structure Node where
  source : ModelBox
  value : Int := 0
  rect : Tile := ⟨0, 0, 0, 0⟩
  series : Nat := 0
  deriving Repr

def tileRect (t : Tile) : Rect := ⟨t.x0, t.y0, t.x1 - t.x0, t.y1 - t.y0⟩

def configInt (m : Model) (key : String) : Option Int :=
  match m.options.config.lookup key with
  | some (.integer n) => some n
  | _ => none

def side (p : Profile) (px unit : Int) : Int :=
  if p == .cell then Int.fdiv (px + unit - 1) unit else px * 64

structure Consts where
  width : Int
  height : Int
  titleBand : Int
  header : Int
  padX : Int
  padY : Int
  innerX : Int
  innerY : Int
  rho : Int
  fuel : Nat

def constants (m : Model) : Consts :=
  let p := m.profile
  let width := (configInt m "nodeWidth").map (fun n => side p (n * 10) 8)
    |>.getD (LayoutConst.treemap_width.get p)
  let height := (configInt m "nodeHeight").map (fun n => side p (n * 10) 16)
    |>.getD (LayoutConst.treemap_height.get p)
  { width, height, titleBand := LayoutConst.treemap_title_band.get p,
    header := LayoutConst.treemap_section_header.get p,
    padX := LayoutConst.treemap_section_padding_x.get p,
    padY := LayoutConst.treemap_section_padding_y.get p,
    innerX := (configInt m "padding").map (fun n => side p n 8)
      |>.getD (LayoutConst.treemap_inner_padding_x.get p),
    innerY := (configInt m "padding").map (fun n => side p n 16)
      |>.getD (LayoutConst.treemap_inner_padding_y.get p),
    rho := LayoutConst.treemap_rho_q30.get p,
    fuel := (LayoutConst.treemap_squarify_cap.get p).toNat }

def labelText (m : Model) (id : String) : String :=
  (m.labels.find? (fun l => l.id == id)).map (·.text) |>.getD ""

def children (nodes : List Node) (id : String) : List Nat :=
  (nodes.zipIdx.filter (fun (n, _) => n.source.parent == id)).map (·.2)

def nodeAt (nodes : List Node) (i : Nat) : Option Node := nodes[i]?

def initialNodes (m : Model) : List Node :=
  let values := m.regionSets.head?.map (·.regions) |>.getD []
  m.boxes.zipIdx.map fun (b, i) =>
    { source := b, value := if b.id == "root" then 0 else (values[i - 1]?).getD 0 }

def parentDepth (nodes : List Node) : Nat → String → Nat
  | 0, _ => 0
  | _ + 1, "" => 0
  | fuel + 1, id =>
    match nodes.find? (fun n => n.source.id == id) with
    | none => 0
    | some n => 1 + parentDepth nodes fuel n.source.parent

def dependencyRanks (nodes : List Node) : List (Nat × Nat) :=
  nodes.zipIdx.map fun (n, i) =>
    (i, parentDepth nodes nodes.length n.source.parent)

def dependencyOrder (nodes : List Node) : List Nat :=
  ((dependencyRanks nodes).mergeSort (fun a b => decide (a.2 ≤ b.2))).map (·.1)

def aggregate (nodes : List Node) : List Node :=
  (dependencyOrder nodes).reverse.foldl (fun acc i =>
    match acc[i]? with
    | none => acc
    | some n =>
      match acc.findIdx? (fun parent => parent.source.id == n.source.parent) with
      | none => acc
      | some j => acc.modify j (fun parent => { parent with value := parent.value + n.value })) nodes

def nodeValue (nodes : List Node) (i : Nat) : Int :=
  (nodes[i]?).map (·.value) |>.getD 0

def childKeyLe (nodes : List Node) (i j : Nat) : Bool :=
  decide (nodeValue nodes i > nodeValue nodes j ∨
    (nodeValue nodes i = nodeValue nodes j ∧ i ≤ j))

def sortedChildren (nodes : List Node) (id : String) : List Nat :=
  (children nodes id).mergeSort (childKeyLe nodes)

def assignSeries (nodes : List Node) : List Node :=
  (dependencyOrder nodes).foldl (fun acc i =>
    match acc[i]? with
    | none => acc
    | some n =>
      let series := if n.source.parent == "root" then
          ((children acc "root").findIdx? (· == i)).getD 0
        else (acc.find? (fun p => p.source.id == n.source.parent)).map (·.series) |>.getD 0
      acc.modify i (fun old => { old with series })) nodes

def tileNodes (c : Consts) (nodes : List Node) : Except LayoutError (List Node) :=
  (dependencyOrder nodes).foldlM (fun acc i => do
    match acc[i]? with
    | none => pure acc
    | some n =>
      let order := sortedChildren acc n.source.id
      if order.isEmpty then pure acc else do
        let values := order.map (fun j => (acc[j]?).map (·.value) |>.getD 0)
        let free := childArea n.rect c.padX c.padY c.header c.innerX c.innerY
        let (cells, _) ← squarify values free c.rho c.fuel
        pure ((order.zip cells).foldl (fun out (j, cell) =>
          out.modify j (fun old => { old with rect := insetCell cell c.innerX c.innerY })) acc)) nodes

structure PlacedLabel where
  source : ModelLabel
  shown : String := ""
  rect : Rect := ⟨0, 0, 0, 0⟩
  size : Int := 0
  align : Align := .middle
  role : TextRole := .label
  style : String := "text"
  italic : Bool := false
  visible : Bool := false

def width (cell : Bool) (text : String) (role : Measure.Role) (size : Int) :
    Except LayoutError Int := do
  let metric ← Chart.XY.metricOf cell role size
  Measure.textWidth metric text.toList

private def fitPrefix (cell : Bool) (text : List Measure.Cluster) (role : Measure.Role)
    (size avail : Int) (lo hi : Nat) : Nat → Except LayoutError Nat
  | 0 => pure lo
  | fuel + 1 => do
    if lo ≥ hi then pure lo else
      let mid := (lo + hi + 1) / 2
      let s := String.ofList (text.take mid).flatten ++ "..."
      let w ← width cell s role size
      if w ≤ avail then fitPrefix cell text role size avail mid hi fuel
      else fitPrefix cell text role size avail lo (mid - 1) fuel

def fit (cell : Bool) (text : String) (avail : Int) (role : Measure.Role) (size : Int) :
    Except LayoutError (Option (String × Int)) := do
  if text.isEmpty then pure none else
    let w ← width cell text role size
    if w ≤ avail then pure (some (text, w)) else
      let ew ← width cell "..." role size
      if ew > avail then pure none else
        let cs := Measure.segment text.toList
        let k ← fitPrefix cell cs role size avail 0 (cs.length - 1) cs.length
        let shown := String.ofList (cs.take k).flatten ++ "..."
        let sw ← width cell shown role size
        pure (some (shown, sw))

def putLabel (l : PlacedLabel) (shown : String) (r : Rect) (size : Int) : PlacedLabel :=
  { l with shown, rect := r, size, visible := true }

def initialLabels (m : Model) : List PlacedLabel :=
  m.labels.map fun l =>
    if l.id == "title" then { source := l, role := .title }
    else if l.id.endsWith ".value" then { source := l, role := .body, style := "text-muted" }
    else { source := l }

def placeTitle (m : Model) (c : Consts) (labels : List PlacedLabel) : Except LayoutError (List PlacedLabel) := do
  match labels.findIdx? (fun l => l.source.id == "title") with
  | none => pure labels
  | some i =>
    match labels[i]? with
    | none => pure labels
    | some l =>
      match ← fit (m.profile == .cell) l.source.text c.width .title 16 with
      | none => pure labels
      | some (shown, w) =>
        let lh := if m.profile == .cell then 1 else 1536
        pure (labels.modify i (fun old => putLabel old shown
          ⟨Int.fdiv (c.width - w) 2, Int.fdiv (c.titleBand - lh) 2, w, lh⟩ 16))

private def labelIndex (labels : List PlacedLabel) (id : String) : Option Nat :=
  labels.findIdx? (fun l => l.source.id == id)

private def sourceText (labels : List PlacedLabel) (i : Option Nat) : String :=
  (i.bind fun j => labels[j]?).map (·.source.text) |>.getD ""

theorem labelIndex_eq_findIdx (labels : List PlacedLabel) (id : String) :
    labelIndex labels id = labels.findIdx? (fun l => l.source.id == id) := rfl

theorem sourceText_eq_lookup (labels : List PlacedLabel) (i : Option Nat) :
    sourceText labels i =
      ((i.bind fun j => labels[j]?).map (·.source.text)).getD "" := rfl

def placeHeader (m : Model) (c : Consts) (n : Node) (labels : List PlacedLabel) :
    Except LayoutError (List PlacedLabel) := do
  let p := m.profile
  let cell := p == .cell
  let r := tileRect n.rect
  let name := labelIndex labels (n.source.id ++ ".name")
  let value := labelIndex labels (n.source.id ++ ".value")
  let ns := Int.fdiv (LayoutConst.treemap_header_label_size.get p) 64
  let vs := Int.fdiv (LayoutConst.treemap_header_value_size.get p) 64
  let lh := if cell then 1 else 1280
  let border := LayoutConst.treemap_header_border.get p
  let top := border + Int.fdiv (c.header - border - lh) 2
  if r.h ≤ top + lh then pure labels else
    let vw ← if value.isSome then width cell (sourceText labels value) .body vs else pure 0
    let vi := LayoutConst.treemap_header_value_inset.get p
    let ni := LayoutConst.treemap_header_label_inset.get p
    let reserve := vi + vw + LayoutConst.treemap_header_gap.get p
    let showValue := value.isSome && vw + vi + ni ≤ r.w &&
      (name.isNone || r.w - ni - reserve ≥ LayoutConst.treemap_header_label_min.get p)
    let avail := if showValue then r.w - ni - reserve else r.w - 2 * ni
    let labels ← match name with
      | none => pure labels
      | some j => do
        match ← fit cell (sourceText labels name) avail .label ns with
        | none => pure labels
        | some (shown, w) => pure (labels.modify j (fun l =>
          { putLabel l shown ⟨r.x + ni, r.y + top, w, lh⟩ ns with align := .start }))
    if showValue then
      match value with
      | none => pure labels
      | some j => pure (labels.modify j (fun l =>
        { putLabel l l.source.text ⟨r.x + r.w - vi - vw, r.y + top, vw, lh⟩ vs
          with align := .«end», italic := true }))
    else pure labels

structure LeafConsts where
  labelSize : Int
  valueSize : Int
  labelMin : Int
  valueMin : Int
  pad : Int
  minDisplay : Int
  spacing : Int

def leafConstants (p : Profile) (dense : Bool) : LeafConsts :=
  if dense then
    ⟨LayoutConst.treemap_leaf_label_size_dense.get p, LayoutConst.treemap_leaf_value_size_dense.get p,
      LayoutConst.treemap_leaf_label_min_dense.get p, LayoutConst.treemap_leaf_value_min_dense.get p,
      LayoutConst.treemap_leaf_pad_dense.get p, LayoutConst.treemap_leaf_min_display_dense.get p,
      LayoutConst.treemap_leaf_spacing_dense.get p⟩
  else
    ⟨LayoutConst.treemap_leaf_label_size.get p, LayoutConst.treemap_leaf_value_size.get p,
      LayoutConst.treemap_leaf_label_min.get p, LayoutConst.treemap_leaf_value_min.get p,
      LayoutConst.treemap_leaf_pad.get p, LayoutConst.treemap_leaf_min_display.get p,
      LayoutConst.treemap_leaf_spacing.get p⟩

private def fitSize (text : String) (availW availH smallest size : Int) : Nat → Except LayoutError Int
  | 0 => pure size
  | fuel + 1 => do
    if size ≤ smallest then pure size else
      let w ← width false text .label size
      if w > availW then fitSize text availW availH smallest (size - 1) fuel
      else pure (max smallest (min size (Int.fdiv availH 64)))

def placeLeaf (m : Model) (lc : LeafConsts) (n : Node) (labels : List PlacedLabel) :
    Except LayoutError (List PlacedLabel) := do
  let name := labelIndex labels (n.source.id ++ ".name")
  let value := labelIndex labels (n.source.id ++ ".value")
  match name with
  | none => pure labels
  | some j =>
    let r := tileRect n.rect
    let aw := r.w - 2 * lc.pad
    let ah := r.h - 2 * lc.pad
    if aw < lc.minDisplay || ah < lc.minDisplay then pure labels else
      let cell := m.profile == .cell
      let ns ← if cell then pure 0 else
        fitSize (sourceText labels name) aw ah (Int.fdiv lc.labelMin 64)
          (Int.fdiv lc.labelSize 64) (Int.fdiv lc.labelSize 64).toNat
      match ← fit cell (sourceText labels name) aw .label ns with
      | none => pure labels
      | some (shown, nw) =>
        let lh := if cell then 1 else 1280
        if !cell && lh > r.h then pure labels else
          let vs := if cell then 0 else max (Int.fdiv lc.valueMin 64)
            (min (Int.fdiv lc.valueSize 64)
              (roundDiv (ns * LayoutConst.treemap_value_scale_percent.get m.profile) 100))
          let pair := 2 * lh + lc.spacing
          let room := pair ≤ (if cell then ah else r.h)
          let vw ← if value.isSome && room then width cell (sourceText labels value) .body vs else pure 0
          let showValue := value.isSome && room && vw ≤ aw
          let rows := if showValue then pair else lh
          let top := if cell then r.y + lc.pad + Int.fdiv (ah - rows) 2
            else r.y + Int.fdiv (r.h - rows) 2
          let out := labels.modify j (fun l => putLabel l shown
            ⟨r.x + lc.pad + Int.fdiv (aw - nw) 2, top, nw, lh⟩ ns)
          if showValue then
            match value with
            | none => pure out
            | some k => pure (out.modify k (fun l => putLabel l l.source.text
              ⟨r.x + lc.pad + Int.fdiv (aw - vw) 2, top + lh + lc.spacing, vw, lh⟩ vs))
          else pure out

private def checkedRect (r : Rect) : Bool :=
  decide (InI32 r.x ∧ InI32 r.y ∧ InI32 r.w ∧ InI32 r.h ∧ InI32 (r.x + r.w) ∧ InI32 (r.y + r.h))

/-- Admission guard computed from the tiled layout before any label is placed:
in the vector profile a childless group box whose leaf rows would sit flush
with its tile top or bottom (`Int.fdiv (r.h - rows) 2 = 0`, i.e.
`r.h - rows ≤ 1`) is rejected, because the written `.name`/`.value` label
rectangles would touch the group frame and fail validator clause 8b. The cell
profile centers through `lc.pad`, so it stays strict without the guard. The
rows figure mirrors `placeLeaf` (1280 alone, or `2 * 1280 + spacing` when the
value label is shown), so only placements that would actually be written are
constrained. -/
def leafGroupLabelVerticalStrict (m : Model) (nodes : List Node) : Bool :=
  if m.profile == .cell then true else
  let lc := leafConstants m.profile
    ((nodes.countP (fun n => n.source.id != "root" && (children nodes n.source.id).isEmpty)) >
      (LayoutConst.treemap_dense_leaves.get m.profile).toNat)
  nodes.all fun n =>
    n.source.id == "root" || n.source.role != .group ||
      !((children nodes n.source.id).isEmpty) ||
      let r := tileRect n.rect
      let aw := r.w - 2 * lc.pad
      let ah := r.h - 2 * lc.pad
      aw < lc.minDisplay || ah < lc.minDisplay || 1280 > r.h ||
      match labelIndex (initialLabels m) (n.source.id ++ ".name") with
      | none => true
      | some j =>
        let nameText := sourceText (initialLabels m) (some j)
        match fitSize nameText aw ah (Int.fdiv lc.labelMin 64) (Int.fdiv lc.labelSize 64)
            (Int.fdiv lc.labelSize 64).toNat with
        | .error _ => true
        | .ok ns =>
          match fit false nameText aw .label ns with
          | .ok none => true
          | .error _ => true
          | .ok (some _) =>
            let value := labelIndex (initialLabels m) (n.source.id ++ ".value")
            let vs := max (Int.fdiv lc.valueMin 64)
              (min (Int.fdiv lc.valueSize 64)
                (roundDiv (ns * LayoutConst.treemap_value_scale_percent.get m.profile) 100))
            let vw := match (if value.isSome && decide (2 * 1280 + lc.spacing ≤ r.h) then
              width false (sourceText (initialLabels m) value) .body vs else pure 0) with
              | .ok k => k
              | .error _ => 0
            let showValue := value.isSome && decide (2 * 1280 + lc.spacing ≤ r.h) &&
              decide (vw ≤ aw)
            let rows := if showValue then 2 * 1280 + lc.spacing else 1280
            decide (2 ≤ r.h - rows)

def layout (m : Model) : Except LayoutError Scene := do
  let c := constants m
  let title := labelText m "title"
  let band := if title.isEmpty then 0 else c.titleBand
  let nodes := assignSeries (aggregate (initialNodes m))
  let nodes := nodes.map fun n => if n.source.id == "root" then
    { n with rect := ⟨0, band, c.width, band + c.height⟩ } else n
  let nodes ← tileNodes c nodes
  if !(leafGroupLabelVerticalStrict m nodes) then throw .domain
  let labels ← placeTitle m c (initialLabels m)
  let leaves := nodes.countP (fun n => n.source.id != "root" && (children nodes n.source.id).isEmpty)
  let lc := leafConstants m.profile (leaves > (LayoutConst.treemap_dense_leaves.get m.profile).toNat)
  let labels ← nodes.foldlM (fun ls n =>
    if n.source.id == "root" then pure ls
    else if (children nodes n.source.id).isEmpty then placeLeaf m lc n ls
    else placeHeader m c n ls) labels
  if !(nodes.all (fun n => checkedRect (tileRect n.rect))) ||
      !(labels.all (fun l => checkedRect l.rect)) ||
      !(decide (InI32 c.width ∧ InI32 (band + c.height))) then throw .overflow
  let boxes := nodes.map fun n =>
    { id := n.source.id, role := n.source.role.id, rect := tileRect n.rect,
      parent := n.source.parent, exclusive := n.source.exclusive : Box }
  let dumpLabels := labels.map fun l =>
    { id := l.source.id, owner := l.source.owner, rect := l.rect,
      lines := if l.visible then [l.shown] else [], text := l.source.text : SceneLabel }
  let groups := [BoxRole.group, BoxRole.node] |>.flatMap fun role =>
    (nodes.filter (fun n => n.source.role == role)).map fun n =>
      let r := tileRect n.rect
      let style := if role == .group then "group"
        else if m.profile == .cell then "series" else "series-tint"
      let paint : Paint := {
        style := style
        series := ⟨n.series % 12, Nat.mod_lt _ (by decide)⟩
      }
      let shape := if n.source.id == "root" || r.w ≤ 0 || r.h ≤ 0 then []
        else [Primitive.rect r paint]
      let texts := (labels.filter (fun l => l.source.owner == n.source.id && l.visible)).map fun l =>
        Primitive.text {
          rect := l.rect
          role := l.role
          size := l.size
          align := l.align
          style := l.style
          lines := [[{ text := l.shown, italic := l.italic }]]
        }
      ({
        role := if role == .group then GroupRole.group else .node
        owner := n.source.id
        items := shape ++ texts
      } : Group)
  pure {
    kind := m.kind
    profile := m.profile
    options := { m.options with direction := .TB }
    canvas := ⟨c.width, band + c.height⟩
    boxes := boxes
    labels := dumpLabels
    items := groups
  }

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem layout_execution (m : Model) (scene : Scene)
    (h : layout m = .ok scene) :
    ∃ nodes,
      tileNodes (constants m)
        ((assignSeries (aggregate (initialNodes m))).map fun n =>
          if n.source.id == "root" then
            { n with rect := ⟨0,
                if (labelText m "title").isEmpty then 0 else (constants m).titleBand,
                (constants m).width,
                (if (labelText m "title").isEmpty then 0 else (constants m).titleBand) +
                  (constants m).height⟩ }
          else n) = .ok nodes ∧
      scene.boxes = nodes.map (fun n =>
        { id := n.source.id, role := n.source.role.id, rect := tileRect n.rect,
          parent := n.source.parent, exclusive := n.source.exclusive : Box }) ∧
      scene.canvas = ⟨(constants m).width,
        (if (labelText m "title").isEmpty then 0 else (constants m).titleBand) +
          (constants m).height⟩ ∧
      scene.routes = [] := by
  unfold layout at h
  dsimp only at h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  split at h
  · cases h
  · obtain ⟨labels0, _, h⟩ := bind_ok h
    obtain ⟨labels, _, h⟩ := bind_ok h
    cases hbad : (((!nodes.all fun n => checkedRect (tileRect n.rect)) ||
        !labels.all fun l => checkedRect l.rect) ||
        !decide (InI32 (constants m).width ∧ InI32
          ((if (labelText m "title").isEmpty = true then 0 else (constants m).titleBand) +
            (constants m).height))) with
    | true =>
      simp only [hbad, ↓reduceIte] at h
      cases h
    | false =>
      simp only [hbad, Bool.false_eq_true, ↓reduceIte] at h
      injection h with heq
      subst scene
      exact ⟨nodes, hnodes, rfl, rfl, rfl⟩

theorem layout_routes_eq_nil (m : Model) (scene : Scene)
    (h : layout m = .ok scene) : scene.routes = [] := by
  obtain ⟨_, _, _, _, hroutes⟩ := layout_execution m scene h
  exact hroutes

/-- The adapter admits only boxes with distinct ids: the dump's parent lookup
    (`LayoutDump.box?`) returns the first box carrying an id, so a repeated id
    would resolve a child's parent to the wrong box and break C3. -/
def boxIdsDistinct (m : Model) : Bool := decide (m.boxes.map (·.id)).Nodup

/-- Follows `parent` links for at most `fuel` steps: `true` when the walk meets a
    root (`""`) or a dangling parent id, `false` when the fuel runs out first,
    which is exactly a cyclic parent chain. -/
def parentChainEnds (boxes : List ModelBox) : Nat → String → Bool
  | _, "" => true
  | 0, _ => false
  | n + 1, id =>
    match boxes.find? (fun b => b.id == id) with
    | none => true
    | some b => parentChainEnds boxes n b.parent

/-- The adapter admits only acyclic parent chains: with `fuel = m.boxes.length`
    a repeated box would exhaust the fuel and be rejected. -/
def parentChainsEnd (m : Model) : Bool :=
  m.boxes.all fun box => parentChainEnds m.boxes m.boxes.length box.parent

/-- The adapter admits a label only when its id names its owner's `.name` or
    `.value` entry, or is the diagram title owned by the root box. The label
    placer looks labels up by id at the owning box's step and copies the
    label's owner verbatim, so any other id would let a label escape its
    owner's scope (C7) or sit outside its owner's frame (C8b). -/
def labelIdsNameOwner (m : Model) : Bool :=
  m.labels.all fun label =>
    label.id == label.owner ++ ".name" || label.id == label.owner ++ ".value" ||
    (label.id == "title" && label.owner == "root")

/-- `fitPrefix` only ever returns an index whose ellipsis-suffixed prefix
    already fit the available width: the `lo` invariant is preserved by every
    recursive step, including fuel exhaustion. -/
theorem fitPrefix_width_le (cell : Bool) (text : List Measure.Cluster)
    (role : Measure.Role) (size avail : Int) :
    ∀ (fuel lo hi k : Nat), fitPrefix cell text role size avail lo hi fuel = .ok k →
      (∀ w, width cell (String.ofList (text.take lo).flatten ++ "...") role size = .ok w → w ≤ avail) →
      ∀ w, width cell (String.ofList (text.take k).flatten ++ "...") role size = .ok w → w ≤ avail := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi k h hlo w hw
      simp only [fitPrefix] at h
      injection h with hk
      subst hk
      exact hlo w hw
  | succ fuel ih =>
      intro lo hi k h hlo w hw
      unfold fitPrefix at h
      dsimp only at h
      split at h
      · rename_i hge
        injection h with hk
        cases hk
        exact hlo w hw
      · obtain ⟨w₀, hw₀, h⟩ := bind_ok h
        split at h
        · rename_i hbound
          apply ih ((lo + hi + 1) / 2) hi k h
          · intro w' hw'
            have heq : w' = w₀ := by
              have := hw'.symm.trans hw₀
              exact Except.ok.inj this
            rw [heq]
            exact hbound
          · exact hw
        · apply ih lo (((lo + hi + 1) / 2) - 1) k h hlo w hw

/-- Every width `fit` reports is within `avail`: the full-text branch checks
    directly, the ellipsis branch checks `"..."` first and `fitPrefix`'s
    invariant bounds the returned prefix width. -/
theorem fit_width_le_avail (cell : Bool) (text : String) (avail : Int)
    (role : Measure.Role) (size : Int) (shown : String) (w : Int)
    (h : fit cell text avail role size = .ok (some (shown, w))) : w ≤ avail := by
  simp only [fit] at h
  cases he : text.isEmpty with
  | true => simp only [he] at h; cases h
  | false =>
      simp only [he] at h
      obtain ⟨w₀, hw₀, h⟩ := bind_ok h
      split at h
      · next hbound =>
          cases h
          omega
      · obtain ⟨ew, hew, h⟩ := bind_ok h
        split at h
        · cases h
        · obtain ⟨k, hklen, h⟩ := bind_ok h
          obtain ⟨sw, hsw, h⟩ := bind_ok h
          cases h
          clear h
          have hlo : ∀ w', width cell (String.ofList ((Measure.segment text.toList).take 0).flatten ++ "...") role size = .ok w' → w' ≤ avail := by
            intro w' hw'
            have hred : String.ofList ((Measure.segment text.toList).take 0).flatten ++ "..." = "..." := by
              simp [List.take_zero]
            rw [hred] at hw'
            have : w' = ew := by
              have := hw'.symm.trans hew
              exact Except.ok.inj this
            rw [this]
            omega
          have hle := fitPrefix_width_le cell (Measure.segment text.toList) role size avail (Measure.segment text.toList).length 0 ((Measure.segment text.toList).length - 1) k hklen hlo w hsw
          omega

end Elegant.Treemap
