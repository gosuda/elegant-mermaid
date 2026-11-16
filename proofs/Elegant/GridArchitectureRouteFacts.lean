import Elegant.GridArchitectureGeometry
import ElegantGeometry.Route
import Elegant.Kinds.Architecture

set_option autoImplicit false

namespace Elegant.Grid.Architecture

theorem compactPoints_head (ps : List Point) :
    (compactPoints ps).head? = ps.head? := by
  induction ps with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp only [compactPoints]
      split
      · rename_i heq
        subst a
        exact ih
      · rfl

theorem compactPoints_orthogonal (ps : List Point)
    (h : Polyline.isOrthogonal ps = true) :
    Polyline.isOrthogonal (compactPoints ps) = true := by
  induction ps with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp only [Polyline.isOrthogonal, Bool.and_eq_true] at h
      have tail := ih h.2
      simp only [compactPoints]
      split
      · exact tail
      · have head := compactPoints_head (b :: rest)
        cases hc : compactPoints (b :: rest) with
        | nil => simp [hc] at head
        | cons c cs =>
          have heq : c = b := by simpa only [hc,List.head?_cons,Option.some.injEq] using head
          subst c
          simpa only [hc,Polyline.isOrthogonal,Bool.and_eq_true] using And.intro h.1 tail

theorem compactPoints_last (ps : List Point) :
    (compactPoints ps).getLast? = ps.getLast? := by
  induction ps with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp only [compactPoints]
      split
      · simpa only [List.getLast?_cons_cons] using ih
      · have nonempty : compactPoints (b :: rest) ≠ [] := by
          intro empty
          have head := compactPoints_head (b :: rest)
          simp only [empty,List.head?_nil,List.head?_cons] at head
          contradiction
        cases tail : compactPoints (b :: rest) with
        | nil => exact False.elim (nonempty tail)
        | cons c cs =>
          simpa only [tail,List.getLast?_cons_cons] using ih

theorem path_endpoints (p : GeometryParams) (pitch : Pitch) (a b : PortEnd) :
    (path p pitch a b).head? = some a.point ∧
      (path p pitch a b).getLast? = some b.point := by
  unfold path
  constructor
  · rw [compactPoints_head]
    split <;> first | rfl | (split <;> first | rfl | (split <;> first | rfl | (split <;> rfl)))
  · rw [compactPoints_last]
    split <;> first | rfl | (split <;> first | rfl | (split <;> first | rfl | (split <;> rfl)))

/-- A port's gutter point lies on its declared gutter line, and its stub uses the
same axis. These are the exact local invariants consumed by the five route cases. -/
def PortAligned (e : PortEnd) : Prop :=
  if e.vertical then e.gutter.x = e.line ∧ e.point.y = e.gutter.y
  else e.gutter.y = e.line ∧ e.point.x = e.gutter.x

theorem port_aligned (p : GeometryParams) (pitch : Pitch) (node : Node)
    (box icon : Span) (position : Cell) (s : Side) (i k : Nat) :
    PortAligned (port p pitch node box icon position s i k) := by
  cases s <;> simp [PortAligned, port]

theorem path_orthogonal (p : GeometryParams) (pitch : Pitch)
    (a b : PortEnd) (ha : PortAligned a) (hb : PortAligned b) :
    Polyline.isOrthogonal (path p pitch a b) = true := by
  unfold path
  apply compactPoints_orthogonal
  cases av : a.vertical <;> cases bv : b.vertical
  all_goals
    simp [PortAligned,av,bv] at ha hb
    split <;> simp_all [Polyline.isOrthogonal]

theorem assigned_ports_aligned (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (edges : List Edge) (resolved : Resolved) (g : Geometry) :
    ∀ ends ∈ assignPorts p pitch nodes edges resolved g,
      PortAligned ends.1 ∧ PortAligned ends.2 := by
  intro ends member
  unfold assignPorts at member
  rcases List.mem_map.mp member with ⟨entry,_,rfl⟩
  exact ⟨port_aligned _ _ _ _ _ _ _ _ _,port_aligned _ _ _ _ _ _ _ _ _⟩

theorem arch_routes_axis_orthogonal (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (edges : List Edge) (resolved : Resolved) (g : Geometry) :
    ∀ route ∈ routes p pitch nodes edges resolved g, Polyline.isOrthogonal route = true := by
  intro route member
  unfold routes at member
  rcases List.mem_map.mp member with ⟨ends,hends,rfl⟩
  have aligned := assigned_ports_aligned p pitch nodes edges resolved g ends hends
  exact path_orthogonal _ _ _ _ aligned.1 aligned.2

theorem routes_have_assigned_endpoints (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (edges : List Edge) (resolved : Resolved) (g : Geometry) :
    ∀ route ∈ routes p pitch nodes edges resolved g,
      Polyline.isOrthogonal route = true ∧
      ∃ ends ∈ assignPorts p pitch nodes edges resolved g,
        route = path p pitch ends.1 ends.2 ∧
        route.head? = some ends.1.point ∧ route.getLast? = some ends.2.point := by
  intro route member
  have orthogonal := arch_routes_axis_orthogonal p pitch nodes edges resolved g route member
  unfold routes at member
  rcases List.mem_map.mp member with ⟨ends,present,rfl⟩
  exact ⟨orthogonal,ends,present,rfl,path_endpoints p pitch ends.1 ends.2⟩

def SpanBoundary (point : Point) (box : Span) : Prop :=
  box.x0 ≤ point.x ∧ point.x ≤ box.x1 ∧ box.y0 ≤ point.y ∧ point.y ≤ box.y1 ∧
    (point.x = box.x0 ∨ point.x = box.x1 ∨ point.y = box.y0 ∨ point.y = box.y1)

theorem along_in_extent (length : Int) (i k : Nat) (nonnegative : 0 ≤ length)
    (slot : i ≤ k) :
    0 ≤ Int.fdiv (((i : Int)+1)*length) ((k : Int)+1) ∧
      Int.fdiv (((i : Int)+1)*length) ((k : Int)+1) ≤ length := by
  have numerator : 0 ≤ ((i : Int)+1)*length :=
    Int.mul_nonneg (by omega) nonnegative
  have denominator : 0 < (k : Int)+1 := by omega
  have product : ((i : Int)+1)*length ≤ length*((k : Int)+1) := by
    have ordered : (i : Int)+1 ≤ (k : Int)+1 := by omega
    have bound := Int.mul_le_mul_of_nonneg_right ordered nonnegative
    simpa only [Int.mul_comm] using bound
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  exact ⟨Int.ediv_nonneg numerator (by omega),Int.ediv_le_of_le_mul denominator product⟩

theorem port_on_box_boundary (p : GeometryParams) (pitch : Pitch) (node : Node)
    (box icon : Span) (position : Cell) (s : Side) (i k : Nat)
    (slot : i ≤ k)
    (width : icon.x0 ≤ icon.x1) (height : icon.y0 ≤ icon.y1)
    (left : box.x0 = icon.x0) (right : box.x1 = icon.x1)
    (top : box.y0 = icon.y0) (bottom : icon.y1 ≤ box.y1) :
    SpanBoundary (port p pitch node box icon position s i k).point box := by
  have selected : (if node.junction then 0 else i) ≤
      (if node.junction then 1 else k) := by
    cases node.junction <;> simp_all
  have horizontal := along_in_extent (icon.x1-icon.x0)
    (if node.junction then 0 else i) (if node.junction then 1 else k) (by omega) selected
  have vertical := along_in_extent (icon.y1-icon.y0)
    (if node.junction then 0 else i) (if node.junction then 1 else k) (by omega) selected
  cases s <;> dsimp only [port, SpanBoundary] <;> omega

theorem assigned_slot_le_length {α : Type} (items : List α) (predicate : α → Bool) :
    (items.findIdx? predicate).getD 0 ≤ items.length := by
  cases found : items.findIdx? predicate with
  | none => simp only [Option.getD_none]; exact Nat.zero_le _
  | some i =>
    have bound := (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
    simp only [Option.getD_some]
    omega

theorem geometry_icon_at (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (groups : List Group) (resolved : Resolved) (n : Nat) (bound : n < nodes.length) :
    (geometry p pitch nodes groups resolved).icons.getD n default =
      let node := nodes.getD n default
      let c := resolved.nodes.getD n default
      sized (c.x*pitch.x + Int.fdiv (pitch.x-node.icon.w) 2)
        (c.y*pitch.y + if node.junction then Int.fdiv (pitch.y-node.icon.h) 2 else pitch.top)
        node.icon := by
  simp only [geometry,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some,Nat.zero_add]

theorem geometry_box_at (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (groups : List Group) (resolved : Resolved) (n : Nat) (bound : n < nodes.length) :
    (geometry p pitch nodes groups resolved).boxes.getD n default =
      let icon := (geometry p pitch nodes groups resolved).icons.getD n default
      let node := nodes.getD n default
      ⟨icon.x0,icon.y0,icon.x1,
        icon.y1+node.label.h+(if node.label.h > 0 then p.thickness else 0)⟩ := by
  simp only [geometry,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some,Nat.zero_add]

theorem geometry_port_on_boundary (p : GeometryParams) (pitch : Pitch)
    (nodes : List Node) (groups : List Group) (resolved : Resolved)
    (n : Nat) (bound : n < nodes.length) (s : Side) (i k : Nat) (slot : i ≤ k)
    (width : 0 ≤ (nodes.getD n default).icon.w)
    (height : 0 ≤ (nodes.getD n default).icon.h)
    (label : 0 ≤ (nodes.getD n default).label.h) (thickness : 0 ≤ p.thickness) :
    SpanBoundary
      (port p pitch (nodes.getD n default)
        ((geometry p pitch nodes groups resolved).boxes.getD n default)
        ((geometry p pitch nodes groups resolved).icons.getD n default)
        (resolved.nodes.getD n default) s i k).point
      ((geometry p pitch nodes groups resolved).boxes.getD n default) := by
  have icon := geometry_icon_at p pitch nodes groups resolved n bound
  have box := geometry_box_at p pitch nodes groups resolved n bound
  apply port_on_box_boundary p pitch _ _ _ _ s i k slot
  · rw [icon]
    simp only [sized]
    omega
  · rw [icon]
    simp only [sized]
    omega
  · rw [box]
  · rw [box]
  · rw [box]
  · rw [box]
    dsimp only
    split <;> omega

theorem assigned_endpoints_on_boxes (p : GeometryParams) (pitch : Pitch)
    (nodes : List Node) (groups : List Group) (edges : List Edge) (resolved : Resolved)
    (nodeSizes : ∀ node ∈ nodes, 0 ≤ node.icon.w ∧ 0 ≤ node.icon.h ∧ 0 ≤ node.label.h)
    (edgeBounds : ∀ edge ∈ edges, edge.a < nodes.length ∧ edge.b < nodes.length)
    (thickness : 0 ≤ p.thickness) :
    ∀ ends ∈ assignPorts p pitch nodes edges resolved (geometry p pitch nodes groups resolved),
      ∃ edge ∈ edges,
        SpanBoundary ends.1.point
          ((geometry p pitch nodes groups resolved).boxes.getD edge.a default) ∧
        SpanBoundary ends.2.point
          ((geometry p pitch nodes groups resolved).boxes.getD edge.b default) := by
  intro ends member
  unfold assignPorts at member
  rcases List.mem_map.mp member with ⟨q,indexed,rfl⟩
  have edgeLookup := List.mem_zipIdx_iff_getElem?.mp indexed
  have edgeMember : q.1 ∈ edges := List.mem_of_getElem? edgeLookup
  have bounds := edgeBounds q.1 edgeMember
  have actual : edges.getD q.2 default = q.1 := by
    simp only [List.getD_eq_getElem?_getD,edgeLookup,Option.getD_some]
  have sizeAt : ∀ n, n < nodes.length →
      0 ≤ (nodes.getD n default).icon.w ∧
      0 ≤ (nodes.getD n default).icon.h ∧
      0 ≤ (nodes.getD n default).label.h := by
    intro n hn
    apply nodeSizes
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
      using List.getElem_mem hn
  refine ⟨q.1,edgeMember,?_,?_⟩
  · simp only [actual,Bool.false_eq_true,↓reduceIte]
    exact geometry_port_on_boundary p pitch nodes groups resolved q.1.a bounds.1 q.1.sideA
      _ _ (assigned_slot_le_length _ _) (sizeAt _ bounds.1).1
      (sizeAt _ bounds.1).2.1 (sizeAt _ bounds.1).2.2 thickness
  · simp only [actual,↓reduceIte]
    exact geometry_port_on_boundary p pitch nodes groups resolved q.1.b bounds.2 q.1.sideB
      _ _ (assigned_slot_le_length _ _) (sizeAt _ bounds.2).1
      (sizeAt _ bounds.2).2.1 (sizeAt _ bounds.2).2.2 thickness

theorem arch_routes_orthogonal (p : GeometryParams) (pitch : Pitch)
    (nodes : List Node) (groups : List Group) (edges : List Edge) (resolved : Resolved)
    (nodeSizes : ∀ node ∈ nodes, 0 ≤ node.icon.w ∧ 0 ≤ node.icon.h ∧ 0 ≤ node.label.h)
    (edgeBounds : ∀ edge ∈ edges, edge.a < nodes.length ∧ edge.b < nodes.length)
    (thickness : 0 ≤ p.thickness) :
    ∀ route ∈ routes p pitch nodes edges resolved (geometry p pitch nodes groups resolved),
      Polyline.isOrthogonal route = true ∧
      ∃ edge ∈ edges, ∃ first last,
        route.head? = some first ∧ route.getLast? = some last ∧
        SpanBoundary first ((geometry p pitch nodes groups resolved).boxes.getD edge.a default) ∧
        SpanBoundary last ((geometry p pitch nodes groups resolved).boxes.getD edge.b default) := by
  intro route member
  have orthogonal := arch_routes_axis_orthogonal p pitch nodes edges resolved _ route member
  unfold routes at member
  rcases List.mem_map.mp member with ⟨ends,present,rfl⟩
  obtain ⟨edge,edgeMember,firstBoundary,lastBoundary⟩ :=
    assigned_endpoints_on_boxes p pitch nodes groups edges resolved nodeSizes edgeBounds
      thickness ends present
  have endpoints := path_endpoints p pitch ends.1 ends.2
  exact ⟨orthogonal,edge,edgeMember,ends.1.point,ends.2.point,
    endpoints.1,endpoints.2,firstBoundary,lastBoundary⟩

theorem public_layout_build (m : Model) (result : Layered.FamilyResult)
    (success : Elegant.Kinds.Architecture.layout m = .ok result) :
    ∃ scene capped, Elegant.Kinds.Architecture.build m = .ok (scene,capped) ∧
      result.scene = scene.projectCellAttachments (Elegant.Kinds.Common.routeMarkers m) ∧
      result.budgetExhausted = capped := by
  let bytes := m.boxes.foldl (fun n b => n+(b.text.getD "").utf8ByteSize) 0 +
    m.labels.foldl (fun n l => n+l.text.utf8ByteSize) 0
  change ((if m.boxes.length > m.options.limits.maxNodes then
      .error (.tooLarge m.options.limits.maxNodes m.boxes.length)
    else if m.routes.length > m.options.limits.maxEdges then
      .error (.tooLarge m.options.limits.maxEdges m.routes.length)
    else if bytes > m.options.limits.maxTextBytes then
      .error (.tooLarge m.options.limits.maxTextBytes bytes)
    else match Elegant.Kinds.Architecture.build m with
      | .error error => .error (.geometry error)
      | .ok (scene,capped) => .ok
        {scene := scene.projectCellAttachments (Elegant.Kinds.Common.routeMarkers m),
          budgetExhausted := capped}) : Except LayoutFailure Layered.FamilyResult) = .ok result at success
  by_cases nodes : m.boxes.length > m.options.limits.maxNodes
  · simp only [nodes,↓reduceIte] at success
    cases success
  · by_cases edges : m.routes.length > m.options.limits.maxEdges
    · simp only [nodes,edges,↓reduceIte] at success
      cases success
    · by_cases text : bytes > m.options.limits.maxTextBytes
      · simp only [nodes,edges,text,↓reduceIte] at success
        cases success
      · simp only [nodes,edges,text,↓reduceIte] at success
        cases built : Elegant.Kinds.Architecture.build m with
        | error error => simp only [built] at success; cases success
        | ok pair =>
          rcases pair with ⟨scene,capped⟩
          simp only [built,Except.ok.injEq] at success
          cases success
          exact ⟨scene,capped,rfl,rfl,rfl⟩

theorem public_layout_dump (m : Model) (result : Layered.FamilyResult)
    (success : Elegant.Kinds.Architecture.layout m = .ok result) :
    ∃ scene capped, Elegant.Kinds.Architecture.build m = .ok (scene,capped) ∧
      result.scene.layoutDump = scene.layoutDump := by
  obtain ⟨scene,capped,built,equal,_⟩ := public_layout_build m result success
  refine ⟨scene,capped,built,?_⟩
  rw [equal,Scene.projectCellAttachments_layoutDump]

theorem public_layout_hardConstraints_of_build (m : Model)
    (result : Layered.FamilyResult)
    (success : Elegant.Kinds.Architecture.layout m = .ok result)
    (builtValid : ∀ scene capped,
      Elegant.Kinds.Architecture.build m = .ok (scene,capped) →
      HardConstraints scene.layoutDump) :
    HardConstraints result.scene.layoutDump := by
  obtain ⟨scene,capped,built,dump⟩ := public_layout_dump m result success
  rw [dump]
  exact builtValid scene capped built

end Elegant.Grid.Architecture
