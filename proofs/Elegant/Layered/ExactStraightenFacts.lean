import Elegant.Layered.ExactFlatC5

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl
namespace ExactStraighten

/-! Shared straightened-exact execution helpers.

The per-edge scene-emission assembly over `componentRunX` / `placeComponentExact`
(straightened route array, packed-route projection, route-key noninterference,
and the straighten-span case analysis) was replayed with private copies in
several leaf proofs. The copies agreed apart from their file-local prefix, so
they live here once, public, under `ExactStraighten`. -/
/-- Routes of an exact-placed component cover the candidate edge decls. -/
theorem placeComponentExact_routes_decls (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run cursor labels loops).routes.map (·.1) =
      cg.edges.map (·.decl) := by
  unfold placeComponentExact
  dsimp only
  rw [List.map_map]
  exact zipIdx_map_comp (·.decl) cg.edges 0

/-- Exact-placed routes keep declaration uniqueness. -/
theorem placeComponentExact_routes_decls_nodup (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (hnd : (cg.edges.map (·.decl)).Nodup) :
    ((placeComponentExact P cg run cursor labels loops).routes.map (·.1)).Nodup := by
  rw [placeComponentExact_routes_decls]
  exact hnd

/-- Exact fold preserves the route array size. -/
theorem components_fold_routes_size (P : Params) (exactIds : List String)
    (inp : Input) (o : Options) (g : Graph) (measured : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentX P exactIds inp o g acc comp measured)
        start = .ok out → out.routes.size = start.routes.size
  | [], start, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | comp :: rest, start, out, h => by
    simp only [List.foldlM_cons] at h
    cases hc : layoutComponentX P exactIds inp o g start comp measured with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact (components_fold_routes_size P exactIds inp o g measured rest next out h).trans
        (layoutComponentX_sizes hc).2.1.symm

/-- Exact ownership: every exact-placed route decl is owned by its component. -/
theorem actualPart_owns {P : Params} {exactIds : List String} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel} {q : List Nat × Part}
    (h : ActualPartX P exactIds inp o g labels q) :
    ∀ d ∈ q.2.routes.map (·.1), ownsDecl g q.1 d := by
  obtain ⟨index, _, run, loops, _, _, _, _, _, hr⟩ := h
  rw [hr, placeComponentExact_routes_decls]
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  exact componentCandidate_edge_owns he

/-- Exact route-key noninterference across distinct actual parts. -/
theorem actual_components_route_keys_disjoint {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel}
    {start out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {a b : List Nat × Part} (ha : a ∈ out.parts) (hb : b ∈ out.parts)
    (hne : a.1 ≠ b.1) {d : Nat} (hd : d ∈ a.2.routes.map (·.1)) :
    d ∉ b.2.routes.map (·.1) := by
  obtain ⟨hm, hall⟩ := actual_components_partsX hempty hfold
  have hca : a.1 ∈ components g := by
    rw [← hm]
    exact List.mem_map_of_mem ha
  have hcb : b.1 ∈ components g := by
    rw [← hm]
    exact List.mem_map_of_mem hb
  intro hd'
  exact components_ownsDecl_disjoint hnd hca hcb hne
    (actualPart_owns (hall a ha) d hd) (actualPart_owns (hall b hb) d hd')

/-- Exact later-route-key noninterference by indexed membership. -/
theorem actual_components_later_route_key_ne {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel}
    {start out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {i j : Nat} {a b : List Nat × Part}
    (ha : out.parts[i]? = some a) (hb : out.parts[j]? = some b) (hij : i < j)
    {d : Nat} (hd : d ∈ a.2.routes.map (·.1)) :
    d ∉ b.2.routes.map (·.1) := by
  obtain ⟨hm, _⟩ := actual_components_partsX hempty hfold
  have hn : (out.parts.map (·.1)).Nodup := by
    rw [hm]
    exact components_entries_nodup g
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, hbj⟩ := List.getElem?_eq_some_iff.mp hb
  have hne : a.1 ≠ b.1 := by
    have hpair := List.pairwise_iff_getElem.mp hn
    have hnij := hpair i j (by simpa using hi) (by simpa using hj) hij
    simpa [hai, hbj] using hnij
  exact actual_components_route_keys_disjoint hempty hfold hnd
    (List.mem_iff_getElem?.mpr ⟨i, ha⟩) (List.mem_iff_getElem?.mpr ⟨j, hb⟩) hne hd

/-- Exact zip-later noninterference for the packed selection. -/
theorem actual_components_zip_later_route_key_ne
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start out : Acc} {positions : List Rect}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {c : Nat} {a : List Nat × Part} {pos : Rect}
    (hsel : (out.parts.zip positions)[c]? = some (a, pos))
    {d : Nat} (hd : d ∈ a.2.routes.map (·.1))
    {q' : (List Nat × Part) × Rect}
    (hq' : q' ∈ (out.parts.zip positions).drop (c + 1)) :
    d ∉ q'.1.2.routes.map (·.1) := by
  obtain ⟨j, hjlt, hjget⟩ :=
    zip_drop_mem_later_getElem? (xs := out.parts) (ys := positions) hq'
  exact actual_components_later_route_key_ne hempty hfold hnd
    (zip_getElem?_left hsel) hjget hjlt hd

theorem actual_components_packAcc_routes_getD
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok mid)
    (hnd : (g.edges.map (·.decl)).Nodup)
    (packed : Pack.State)
    (hpack : packAcc P o mid = .ok out)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hget_pair : (mid.parts.zip packed.boxes)[c]? = some q)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < mid.routes.size) :
    out.routes.getD k d = pts.map (shiftPoint q.2.x q.2.y) := by
  have hsel : (mid.parts.zip packed.boxes)[c]? = some (q.1, q.2) := hget_pair
  have hmem : k ∈ q.1.2.routes.map (·.1) := by
    have hp : (k, pts) ∈ q.1.2.routes := List.mem_iff_getElem?.mpr ⟨i, hget_route⟩
    exact List.mem_map_of_mem hp
  refine packAcc_routes_getD hpack packed hpacked c q hget_pair i k pts d hget_route hnodup hsize ?_
  intro q' hq'
  exact actual_components_zip_later_route_key_ne hempty hfold hnd hsel hmem hq'

theorem straightenStep_size {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
    {st st' : StraightenWork} {i : Nat} (h : straightenStep ctx boxes st i = .ok st') :
    st'.routes.size = st.routes.size := by
  obtain ⟨plan, _, h2⟩ := bind_ok h
  cases plan with
  | none =>
    have he := Except.ok.inj h2
    subst he
    rfl
  | some plan =>
    obtain ⟨routing, decl, newPoints⟩ := plan
    have he := Except.ok.inj h2
    subst he
    simp only
    split <;> simp

theorem straightenFrom_size {ctx : StraightenCtx} {boxes : List (Bool × Rect)} :
    ∀ (n start : Nat) (st st' : StraightenWork),
      straightenFrom ctx boxes n start st = .ok st' → st'.routes.size = st.routes.size := by
  intro n
  induction n with
  | zero =>
    intro start st st' h
    have he := Except.ok.inj h
    subst he
    rfl
  | succ n ih =>
    intro start st st' h
    obtain ⟨st1, h1, h2⟩ := bind_ok h
    have e1 := straightenStep_size h1
    have e2 := ih (start + 1) st1 st' h2
    omega

theorem straightenComponent_size {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
    {routes out : Array (List Point)} (h : straightenComponent ctx boxes routes = .ok out) :
    out.size = routes.size := by
  unfold straightenComponent at h
  obtain ⟨st, h1, h2⟩ := bind_ok h
  have he := Except.ok.inj h2
  subst he
  exact straightenFrom_size _ _ _ _ h1

theorem straightenParts_size {boxesOf : StraightenCtx → List Nat → List (Bool × Rect)}
    {rects : Array Rect} :
    ∀ (parts : List (List Nat × Part)) (routes out : Array (List Point)),
      straightenParts boxesOf rects parts routes = .ok out → out.size = routes.size := by
  intro parts
  induction parts with
  | nil =>
    intro routes out h
    have he := Except.ok.inj h
    subst he
    rfl
  | cons q rest ih =>
    intro routes out h
    simp only [straightenParts] at h
    cases hoff : straightenOffset q.1 q.2 rects with
    | none =>
      simp only [hoff] at h
      exact ih routes out h
    | some off =>
      obtain ⟨ctx0, ox, oy⟩ := off
      simp only [hoff] at h
      cases hcomp : straightenComponent { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
        (boxesOf ctx0 q.1) routes with
      | error e =>
        simp only [hcomp] at h
        cases h
      | ok updated =>
        simp only [hcomp] at h
        have e1 := straightenComponent_size hcomp
        have e2 := ih updated out h
        omega

theorem straightenAcc_routes_size {inp : Input} {acc s : Acc}
    (h : straightenAcc inp acc = .ok s) : s.routes.size = acc.routes.size := by
  unfold straightenAcc at h
  obtain ⟨routes, h1, h2⟩ := bind_ok h
  have he := Except.ok.inj h2
  subst he
  simp only
  exact straightenParts_size _ _ _ h1

theorem straight_canvasH {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.straightAcc.canvasH = execution.packedAcc.canvasH :=
  (straightenAcc_fields execution.straight_eq).2.2.2.2

theorem straight_points_of_scene {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {k : Nat} {id fromId toId : String} {orthogonal : Bool} {pts : List Point}
    (h : res.scene.routes[k]? = some (Route.mk id fromId toId orthogonal
        (pts.map fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)))) :
    execution.straightAcc.routes.getD k [] = pts := by
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length _ _ _ _ _ _
  have hk : k < inp.routes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp h).1
    rw [hlen] at hlt
    exact hlt
  have hH : execution.straightAcc.canvasH = execution.packedAcc.canvasH :=
    straight_canvasH execution
  have hs0 := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured k hk
  rw [← execution.scene_eq] at hs0
  rw [hH] at hs0
  have hpts1 : (res.scene.routes[k]?).map (·.points) = some (pts.map fun p =>
      shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH p)) := by
    rw [h]
    rfl
  have hpts2 : (res.scene.routes[k]?).map (·.points) = some
      ((execution.straightAcc.routes.getD k []).map fun p =>
        shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)) := by
    rw [hs0]
    rfl
  have hmap : (execution.straightAcc.routes.getD k []).map (fun p =>
      shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH p)) =
      pts.map (fun p =>
        shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)) :=
    Option.some.inj (hpts2.symm.trans hpts1)
  have hfinj : ∀ a b : Point, (fun p =>
      shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH p)) a =
      (fun p =>
        shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)) b → a = b := by
    intro a b hab
    have hab' : shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH a) =
        shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH b) := hab
    have h1 : orientPoint o.direction execution.packedAcc.canvasH a =
        orientPoint o.direction execution.packedAcc.canvasH b :=
      (shiftPoint_inj _ _ _ _).mp hab'
    exact (orientPoint_inj _ _ _ _).mp h1
  have hcancel : ∀ (f : Point → Point), (∀ a b : Point, f a = f b → a = b) →
      ∀ (a b : List Point), a.map f = b.map f → a = b := by
    intro f hfinj a b h
    induction a generalizing b with
    | nil =>
      cases b with
      | nil => rfl
      | cons _ _ =>
        simp only [List.map_nil, List.map_cons] at h
        cases h
    | cons x xs ih =>
      cases b with
      | nil =>
        simp only [List.map_cons, List.map_nil] at h
        cases h
      | cons y ys =>
        have hhead : f x = f y := Option.some.inj (congrArg List.head? h)
        have htail : xs.map f = ys.map f := congrArg List.tail h
        have hxy : x = y := hfinj _ _ hhead
        have hrest : xs = ys := ih _ htail
        rw [hxy, hrest]
  exact hcancel _ hfinj _ _ hmap

theorem componentRunX_declInv {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (_hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hnorm : ∃ ranks normalized, normalize cg ranks = .ok normalized ∧
      run.proper.edges = normalized.edges ∧ run.proper.chains = normalized.chains) :
    DeclInv cg.edges run.proper := by
  obtain ⟨ranks, normalized, hn, he, _⟩ := hnorm
  unfold DeclInv
  rw [he]
  exact normalize_declInv hn

theorem straightenOffset_ctx {comp : List Nat} {part : Part} {rects : Array Rect}
    {ctx0 : StraightenCtx} {ox oy : Int}
    (h : straightenOffset comp part rects = some (ctx0, ox, oy)) :
    part.straighten = some ctx0 := by
  unfold straightenOffset at h
  cases h1 : part.straighten with
  | none =>
    simp only [h1] at h
    cases h
  | some c =>
    cases h2 : comp.zip part.rects with
    | nil =>
      simp only [h1, h2] at h
      cases h
    | cons pr rest =>
      cases h3 : rects[pr.1]? with
      | none =>
        simp only [h1, h2, h3] at h
        cases h
      | some base =>
        simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, _⟩, _⟩ := h
        exact rfl

theorem straightSpanOf_inv {ctx : StraightenCtx} {routing : Routing} {i : Nat}
    {span : StraightSpan} (h : straightSpanOf ctx routing i = .ok (some span)) :
    ∃ e, ctx.proper.edges[i]? = some e ∧ straightEdgeEligible ctx routing i e = true ∧
      span.decl = ctx.decls.getD e.original 0 ∧ span.top < span.bottom := by
  unfold straightSpanOf at h
  cases he : ctx.proper.edges[i]? with
  | none =>
    simp only [he] at h
    cases h
  | some e =>
    simp only [he] at h
    cases hel : !straightEdgeEligible ctx routing i e with
    | true =>
      simp only [hel] at h
      cases h
    | false =>
      simp only [hel] at h
      cases hgeom : straightGeom ctx routing i e with
      | mk tw hw th hh tailLeft headLeft lo hi cx =>
        simp only [hgeom] at h
        by_cases hlo : lo > hi
        · rw [ite_eq_left hlo] at h
          cases h
        · rw [ite_eq_right hlo] at h
          obtain ⟨pin, _, h⟩ := bind_ok h
          obtain ⟨top, _, h⟩ := bind_ok h
          obtain ⟨bottom, _, h⟩ := bind_ok h
          by_cases hge : top ≥ bottom
          · rw [ite_eq_left hge] at h
            cases h
          · rw [ite_eq_right hge] at h
            obtain ⟨column, _, h⟩ := bind_ok h
            have hlt : top < bottom := by omega
            have hs := Option.some.inj (Except.ok.inj h)
            have helig : straightEdgeEligible ctx routing i e = true := by
              cases hb : straightEdgeEligible ctx routing i e with
              | true => rfl
              | false =>
                simp only [hb] at hel
                cases hel
            subst hs
            exact ⟨e, rfl, helig, rfl, hlt⟩

theorem straightenStep_span {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
    {st st' : StraightenWork} {i : Nat} (h : straightenStep ctx boxes st i = .ok st') :
    ∀ (decl : Nat) (pts : List Point), st'.routes[decl]? = some pts →
      st.routes[decl]? = some pts ∨
      ∃ (routing : Routing) (j : Nat) (span : StraightSpan),
        straightSpanOf ctx routing j = .ok (some span) ∧ span.decl = decl ∧ pts = span.points := by
  obtain ⟨plan, hp, h⟩ := bind_ok h
  cases plan with
  | none =>
    have he := Except.ok.inj h
    subst he
    intro decl pts hj
    exact Or.inl hj
  | some plan =>
    obtain ⟨_, decl', pts'⟩ := plan
    obtain ⟨span, hspan, _, hdecl, hpts⟩ := straightenPlan_points hp
    have he := Except.ok.inj h
    subst he
    intro decl pts hj
    by_cases hd : decl' < st.routes.size
    · rw [dite_eq_left hd, Array.getElem?_set] at hj
      split at hj
      · obtain ⟨rfl⟩ := Option.some.inj hj
        exact Or.inr ⟨st.routing, i, span, hspan, by omega, hpts⟩
      · exact Or.inl hj
    · rw [dite_eq_right hd] at hj
      exact Or.inl hj

theorem straightenFrom_span {ctx : StraightenCtx} {boxes : List (Bool × Rect)} :
    ∀ (n start : Nat) (st st' : StraightenWork),
      straightenFrom ctx boxes n start st = .ok st' →
      ∀ (decl : Nat) (pts : List Point), st'.routes[decl]? = some pts →
        st.routes[decl]? = some pts ∨
        ∃ (routing : Routing) (i : Nat) (span : StraightSpan),
          straightSpanOf ctx routing i = .ok (some span) ∧ span.decl = decl ∧ pts = span.points := by
  intro n
  induction n with
  | zero =>
    intro start st st' h decl pts hj
    have he := Except.ok.inj h
    subst he
    exact Or.inl hj
  | succ n ih =>
    intro start st st' h decl pts hj
    obtain ⟨st1, h1, h2⟩ := bind_ok h
    cases ih (start + 1) st1 st' h2 decl pts hj with
    | inl hmid => exact straightenStep_span h1 decl pts hmid
    | inr hw => exact Or.inr hw

theorem straightenComponent_span {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
    {routes out : Array (List Point)} (h : straightenComponent ctx boxes routes = .ok out) :
    ∀ (decl : Nat) (pts : List Point), out[decl]? = some pts →
      routes[decl]? = some pts ∨
      ∃ (routing : Routing) (i : Nat) (span : StraightSpan),
        straightSpanOf ctx routing i = .ok (some span) ∧ span.decl = decl ∧ pts = span.points := by
  obtain ⟨st, h1, h2⟩ := bind_ok h
  have he := Except.ok.inj h2
  subst he
  intro decl pts hj
  cases straightenFrom_span ctx.proper.edges.length 0 { routing := ctx.routing, routes } st h1
    decl pts hj with
  | inl hold => exact Or.inl hold
  | inr hw => exact Or.inr hw

theorem straightenParts_span {boxesOf : StraightenCtx → List Nat → List (Bool × Rect)}
    {rects : Array Rect} :
    ∀ (parts : List (List Nat × Part)) (routes out : Array (List Point)),
      straightenParts boxesOf rects parts routes = .ok out →
      ∀ (decl : Nat) (pts : List Point), out[decl]? = some pts →
        routes[decl]? = some pts ∨
        ∃ (q : List Nat × Part) (ctx0 : StraightenCtx) (ox oy : Int) (routing : Routing)
          (i : Nat) (span : StraightSpan),
          q ∈ parts ∧ q.2.straighten = some ctx0 ∧
          straightenOffset q.1 q.2 rects = some (ctx0, ox, oy) ∧
          straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing i =
            .ok (some span) ∧
          span.decl = decl ∧ pts = span.points := by
  intro parts
  induction parts with
  | nil =>
    intro routes out h decl pts hi
    have he := Except.ok.inj h
    subst he
    exact Or.inl hi
  | cons q rest ih =>
    intro routes out h decl pts hi
    simp only [straightenParts] at h
    cases hoff : straightenOffset q.1 q.2 rects with
    | none =>
      simp only [hoff] at h
      cases ih routes out h decl pts hi with
      | inl hold => exact Or.inl hold
      | inr hw =>
        obtain ⟨q', ctx0, ox, oy, routing, i, span, hmem, hctx, hoff', hspan, hdecl, hpts⟩ := hw
        exact Or.inr ⟨q', ctx0, ox, oy, routing, i, span, List.mem_cons_of_mem _ hmem,
          hctx, hoff', hspan, hdecl, hpts⟩
    | some off =>
      obtain ⟨ctx0, ox, oy⟩ := off
      simp only [hoff] at h
      cases hcomp : straightenComponent { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
        (boxesOf ctx0 q.1) routes with
      | ok updated =>
        rw [hcomp] at h
        cases ih updated out h decl pts hi with
        | inl hmid =>
          cases straightenComponent_span hcomp decl pts hmid with
          | inl hold => exact Or.inl hold
          | inr hw =>
            obtain ⟨routing, i, span, hspan, hdecl, hpts⟩ := hw
            have hctx := straightenOffset_ctx hoff
            exact Or.inr ⟨q, ctx0, ox, oy, routing, i, span, List.mem_cons_self,
              hctx, hoff, hspan, hdecl, hpts⟩
        | inr hw =>
          obtain ⟨q', ctx0', ox', oy', routing, i, span, hmem, hctx, hoff', hspan, hdecl,
            hpts⟩ := hw
          exact Or.inr ⟨q', ctx0', ox', oy', routing, i, span, List.mem_cons_of_mem _ hmem,
            hctx, hoff', hspan, hdecl, hpts⟩
      | error e =>
        simp only [hcomp] at h
        cases h

theorem foldl_acc_parts (step : Acc → ((List Nat × Part) × Rect) → Acc)
    (hstep : ∀ s q, (step s q).parts = s.parts) :
    ∀ (pairs : List (((List Nat) × Part) × Rect)) (start : Acc),
      (pairs.foldl step start).parts = start.parts := by
  intro pairs
  induction pairs with
  | nil => intro start; rfl
  | cons q qs ih =>
    intro start
    rw [List.foldl_cons]
    exact (ih (step start q)).trans (hstep start q)

theorem packAcc_parts_eq {P : Params} {o : Options} {acc out : Acc}
    (h : packAcc P o acc = .ok out) : out.parts = acc.parts := by
  unfold packAcc at h
  obtain ⟨packed, _, h2⟩ := bind_ok h
  have he := Except.ok.inj h2
  subst out
  refine foldl_acc_parts _ ?_ _ _
  intro s q
  rfl

theorem route_cases {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (normSrc : ∀ {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions}, componentRunX execution.params exact cg labels
        orderOptions = .ok run →
      ∃ ranks normalized, normalize cg ranks = .ok normalized ∧
        run.proper.edges = normalized.edges ∧ run.proper.chains = normalized.chains)
    {key : Nat} {pts : List Point}
    (hpts : execution.straightAcc.routes[key]? = some pts) :
    execution.packedAcc.routes[key]? = some pts ∨ Installed execution.packedAcc key pts := by
  obtain ⟨routes, h1, h2⟩ := bind_ok execution.straight_eq
  have heq := Except.ok.inj h2
  have hst : routes = execution.straightAcc.routes := congrArg Acc.routes heq
  simp only [straightenRoutes] at h1
  have hpts' : routes[key]? = some pts := by
    rw [hst]
    exact hpts
  cases straightenParts_span execution.packedAcc.parts execution.packedAcc.routes routes h1
      key pts hpts' with
  | inl hold => exact Or.inl hold
  | inr hw =>
    obtain ⟨qI, ctx0, ox, oy, routing, i, span, hmem, hctx, hoff, hspan, hdecl, hpts''⟩ := hw
    obtain ⟨e, he0, helig, hdecl0, _hTopLt⟩ := straightSpanOf_inv hspan
    have hTailNe : e.tail ≠ e.head := by
      unfold straightEdgeEligible at helig
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hNe⟩, _⟩, _⟩ := helig
      intro hcon
      rw [hcon] at hNe
      simp at hNe
    have hqmem : qI ∈ execution.componentsAcc.parts := by
      have hp := packAcc_parts_eq execution.packed_eq
      rw [hp] at hmem
      exact hmem
    obtain ⟨index, chosen, runI, loopsI, areaI, _, _, _, hrunI, _, hplaceI⟩ :=
      (actual_components_parts_geometryX (by rfl) execution.components_eq).2 qI hqmem
    have hstraightC : (placeComponentExact execution.params
        (componentCandidate execution.graph qI.1 index) runI 0 execution.measured
        loopsI).straighten = some ctx0 := by
      have hc := hctx
      rw [hplaceI] at hc
      exact hc
    unfold placeComponentExact at hstraightC
    dsimp only at hstraightC
    have hctxEq := Option.some.inj hstraightC
    have hproperEq : ctx0.proper = runI.proper :=
      (congrArg StraightenCtx.proper hctxEq.symm).trans rfl
    have hdeclsEq : ctx0.decls =
        (componentCandidate execution.graph qI.1 index).edges.map (·.decl) :=
      (congrArg StraightenCtx.decls hctxEq.symm).trans rfl
    have he0proper : ctx0.proper.edges[i]? = some e := he0
    have he0' : runI.proper.edges[i]? = some e := hproperEq ▸ he0proper
    have hmemE : e ∈ runI.proper.edges := List.mem_of_getElem? he0'
    obtain ⟨ge, hge, hdeclge⟩ := componentRunX_declInv hrunI (normSrc hrunI) e hmemE
    have hmap : ((componentCandidate execution.graph qI.1 index).edges.map
        (·.decl))[e.original]? = some ge.decl := by
      simp only [List.getElem?_map, hge, Option.map_some]
    have hget : ((componentCandidate execution.graph qI.1 index).edges.map
        (·.decl)).getD e.original 0 = ge.decl := by
      simp only [List.getD_eq_getElem?_getD, hmap, Option.getD_some]
    have hdecl0' : span.decl = ctx0.decls.getD e.original 0 := hdecl0
    have hdeclCtx : span.decl =
        ((componentCandidate execution.graph qI.1 index).edges.map (·.decl)).getD
          e.original 0 := by
      rw [hdecl0', hdeclsEq]
    have hm1 : e.decl = ((componentCandidate execution.graph qI.1 index).edges.map
      (·.decl)).getD e.original 0 := hdeclge.trans hget.symm
    have hkey : e.decl = key := hm1.trans (hdeclCtx.symm.trans hdecl)
    exact Or.inr ⟨qI, ctx0, ox, oy, i, e, span, hmem, hctx, hoff, he0proper, hkey, hTailNe,
      routing, hspan, hpts''⟩

theorem corridor_misses_tail {c t b : Int} {r : Rect}
    (htop : t = r.y + r.h) (hlt : t < b) :
    ¬ Polyline.hitsRect [⟨c, t⟩, ⟨c, b⟩] r := by
  intro hHit
  obtain ⟨_, _, hmiss⟩ := hHit
  have hmin : min t b = t := Int.min_eq_left (Int.le_of_lt hlt)
  have hle : r.y + r.h ≤ min t b := by
    rw [hmin, htop]
    exact Int.le_refl _
  have hseg : Polyline.segMisses ⟨c, t⟩ ⟨c, b⟩ r :=
    Or.inr (Or.inr (Or.inr (Or.inl hle)))
  have hmissAll : Polyline.allSegsMiss [⟨c, t⟩, ⟨c, b⟩] r := ⟨hseg, trivial⟩
  exact hmiss hmissAll

theorem corridor_misses_head {c t b : Int} {r : Rect}
    (hbot : b = r.y) (hlt : t < b) :
    ¬ Polyline.hitsRect [⟨c, t⟩, ⟨c, b⟩] r := by
  intro hHit
  obtain ⟨_, _, hmiss⟩ := hHit
  have hmax : max t b = b := Int.max_eq_right (Int.le_of_lt hlt)
  have hle : max t b ≤ r.y := by
    rw [hmax, hbot]
    exact Int.le_refl _
  have hseg : Polyline.segMisses ⟨c, t⟩ ⟨c, b⟩ r :=
    Or.inr (Or.inr (Or.inl hle))
  have hmissAll : Polyline.allSegsMiss [⟨c, t⟩, ⟨c, b⟩] r := ⟨hseg, trivial⟩
  exact hmiss hmissAll

theorem straightenStep_span_clear {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
    {st st' : StraightenWork} {i : Nat} (h : straightenStep ctx boxes st i = .ok st') :
    ∀ (decl : Nat) (pts : List Point), st'.routes[decl]? = some pts →
      st.routes[decl]? = some pts ∨
      ∃ (routing : Routing) (j : Nat) (span : StraightSpan),
        straightSpanOf ctx routing j = .ok (some span) ∧ span.decl = decl ∧ pts = span.points ∧
        straightStepClear boxes span.tailRect span.headRect span.top span.bottom span.column = true := by
  obtain ⟨plan, hp, h⟩ := bind_ok h
  cases plan with
  | none =>
    have he := Except.ok.inj h
    subst he
    intro decl pts hj
    exact Or.inl hj
  | some plan =>
    obtain ⟨_, decl', pts'⟩ := plan
    obtain ⟨span, hspan, _, hdecl, hpts, hclr⟩ := straightenPlan_clear hp
    have he := Except.ok.inj h
    subst he
    intro decl pts hj
    by_cases hd : decl' < st.routes.size
    · rw [dite_eq_left hd, Array.getElem?_set] at hj
      split at hj
      · obtain ⟨rfl⟩ := Option.some.inj hj
        exact Or.inr ⟨st.routing, i, span, hspan, by omega, hpts, hclr⟩
      · exact Or.inl hj
    · rw [dite_eq_right hd] at hj
      exact Or.inl hj

theorem straightenFrom_span_clear {ctx : StraightenCtx} {boxes : List (Bool × Rect)} :
    ∀ (n start : Nat) (st st' : StraightenWork),
      straightenFrom ctx boxes n start st = .ok st' →
      ∀ (decl : Nat) (pts : List Point), st'.routes[decl]? = some pts →
        st.routes[decl]? = some pts ∨
        ∃ (routing : Routing) (i : Nat) (span : StraightSpan),
          straightSpanOf ctx routing i = .ok (some span) ∧ span.decl = decl ∧ pts = span.points ∧
          straightStepClear boxes span.tailRect span.headRect span.top span.bottom span.column = true := by
  intro n
  induction n with
  | zero =>
    intro start st st' h decl pts hj
    have he := Except.ok.inj h
    subst he
    exact Or.inl hj
  | succ n ih =>
    intro start st st' h decl pts hj
    obtain ⟨st1, h1, h2⟩ := bind_ok h
    cases ih (start + 1) st1 st' h2 decl pts hj with
    | inl hmid => exact straightenStep_span_clear h1 decl pts hmid
    | inr hw => exact Or.inr hw

theorem straightenComponent_span_clear {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
    {routes out : Array (List Point)} (h : straightenComponent ctx boxes routes = .ok out) :
    ∀ (decl : Nat) (pts : List Point), out[decl]? = some pts →
      routes[decl]? = some pts ∨
      ∃ (routing : Routing) (i : Nat) (span : StraightSpan),
        straightSpanOf ctx routing i = .ok (some span) ∧ span.decl = decl ∧ pts = span.points ∧
        straightStepClear boxes span.tailRect span.headRect span.top span.bottom span.column = true := by
  obtain ⟨st, h1, h2⟩ := bind_ok h
  have he := Except.ok.inj h2
  subst he
  intro decl pts hj
  cases straightenFrom_span_clear ctx.proper.edges.length 0 { routing := ctx.routing, routes } st h1
    decl pts hj with
  | inl hold => exact Or.inl hold
  | inr hw => exact Or.inr hw

theorem straightenParts_span_clear {boxesOf : StraightenCtx → List Nat → List (Bool × Rect)} {rects : Array Rect} :
    ∀ (parts : List (List Nat × Part)) (routes out : Array (List Point)),
      straightenParts boxesOf rects parts routes = .ok out →
      ∀ (decl : Nat) (pts : List Point), out[decl]? = some pts →
        routes[decl]? = some pts ∨
        ∃ (q : List Nat × Part) (ctx0 : StraightenCtx) (ox oy : Int) (routing : Routing)
          (i : Nat) (span : StraightSpan),
          q ∈ parts ∧ q.2.straighten = some ctx0 ∧
          straightenOffset q.1 q.2 rects = some (ctx0, ox, oy) ∧
          straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing i =
            .ok (some span) ∧
          span.decl = decl ∧ pts = span.points ∧
          straightStepClear (boxesOf ctx0 q.1) span.tailRect span.headRect span.top span.bottom span.column = true := by
  intro parts
  induction parts with
  | nil =>
    intro routes out h decl pts hi
    have he := Except.ok.inj h
    subst he
    exact Or.inl hi
  | cons q rest ih =>
    intro routes out h decl pts hi
    simp only [straightenParts] at h
    cases hoff : straightenOffset q.1 q.2 rects with
    | none =>
      simp only [hoff] at h
      cases ih routes out h decl pts hi with
      | inl hold => exact Or.inl hold
      | inr hw =>
        obtain ⟨q', ctx0, ox, oy, routing, i, span, hmem, hctx, hoff', hspan, hdecl, hpts,
          hclr⟩ := hw
        exact Or.inr ⟨q', ctx0, ox, oy, routing, i, span, List.mem_cons_of_mem _ hmem,
          hctx, hoff', hspan, hdecl, hpts, hclr⟩
    | some off =>
      obtain ⟨ctx0, ox, oy⟩ := off
      simp only [hoff] at h
      cases hcomp : straightenComponent { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
        (boxesOf ctx0 q.1) routes with
      | ok updated =>
        rw [hcomp] at h
        cases ih updated out h decl pts hi with
        | inl hmid =>
          cases straightenComponent_span_clear hcomp decl pts hmid with
          | inl hold => exact Or.inl hold
          | inr hw =>
            obtain ⟨routing, i, span, hspan, hdecl, hpts, hclr⟩ := hw
            have hctx := straightenOffset_ctx hoff
            exact Or.inr ⟨q, ctx0, ox, oy, routing, i, span, List.mem_cons_self,
              hctx, hoff, hspan, hdecl, hpts, hclr⟩
        | inr hw =>
          obtain ⟨q', ctx0', ox', oy', routing, i, span, hmem, hctx, hoff', hspan, hdecl,
            hpts, hclr⟩ := hw
          exact Or.inr ⟨q', ctx0', ox', oy', routing, i, span, List.mem_cons_of_mem _ hmem,
            hctx, hoff', hspan, hdecl, hpts, hclr⟩
      | error e =>
        simp only [hcomp] at h
        cases h

theorem installed_global_mem {acc : Acc} {inp : Input} {vkey : Nat} {rect : Rect}
    {mbox : ModelBox} (hrect : acc.rects[vkey]? = some rect)
    (hbox : inp.boxes[vkey]? = some mbox) :
    (decide (mbox.role == BoxRole.node), rect) ∈ installed_global_boxes acc inp := by
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hrect
  have hmemRange : vkey ∈ List.range acc.rects.size := List.mem_range.mpr hlt
  have hfun : (match acc.rects[vkey]?, inp.boxes[vkey]? with
      | some r, some m => some (decide (m.role == BoxRole.node), r)
      | _, _ => none) = some (decide (mbox.role == BoxRole.node), rect) := by
    rw [hrect, hbox]
  have hmem : (decide (mbox.role == BoxRole.node), rect) ∈
      ((List.range acc.rects.size).filterMap fun v =>
        match acc.rects[v]?, inp.boxes[v]? with
        | some r, some m => some (decide (m.role == BoxRole.node), r)
        | _, _ => none) :=
    List.mem_filterMap.mpr ⟨vkey, hmemRange, hfun⟩
  unfold installed_global_boxes
  exact hmem

theorem route_cases_clear {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (normSrc : ∀ {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions}, componentRunX execution.params exact cg labels
        orderOptions = .ok run →
      ∃ ranks normalized, normalize cg ranks = .ok normalized ∧
        run.proper.edges = normalized.edges ∧ run.proper.chains = normalized.chains)
    {key : Nat} {pts : List Point}
    (hpts : execution.straightAcc.routes[key]? = some pts) :
    execution.packedAcc.routes[key]? = some pts ∨
    ∃ (q : List Nat × Part) (ctx0 : StraightenCtx) (ox oy : Int) (i : Nat) (e : ProperEdge)
      (routing : Routing) (span : StraightSpan),
      q ∈ execution.packedAcc.parts ∧ q.2.straighten = some ctx0 ∧
      straightenOffset q.1 q.2 execution.packedAcc.rects = some (ctx0, ox, oy) ∧
      ctx0.proper.edges[i]? = some e ∧ e.decl = key ∧
      straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing i =
        .ok (some span) ∧ pts = span.points ∧
      straightStepClear (straightenPartBoxes inp execution.packedAcc ctx0 q.1) span.tailRect
        span.headRect span.top span.bottom span.column = true := by
  obtain ⟨routes, h1, h2⟩ := bind_ok execution.straight_eq
  have heq := Except.ok.inj h2
  have hst : routes = execution.straightAcc.routes := congrArg Acc.routes heq
  simp only [straightenRoutes] at h1
  have hpts' : routes[key]? = some pts := by
    rw [hst]
    exact hpts
  cases straightenParts_span_clear execution.packedAcc.parts execution.packedAcc.routes routes h1 key pts hpts' with
  | inl hold => exact Or.inl hold
  | inr hw =>
    obtain ⟨q, ctx0, ox, oy, routing, i, span, hmem, hctx, hoff, hspan, hdecl, hpts'',
      hclr⟩ := hw
    obtain ⟨e, he, helig, hdeclshape, _⟩ := straightSpanOf_inv hspan
    have he0 : ctx0.proper.edges[i]? = some e := he
    have hdecl0 : span.decl = ctx0.decls.getD e.original 0 := hdeclshape
    have hne : e.tail ≠ e.head := by
      unfold straightEdgeEligible at helig
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hNe⟩, _⟩, _⟩ := helig
      intro hcon
      rw [hcon] at hNe
      simp at hNe
    have hm1 : e.decl = ctx0.decls.getD e.original 0 := by
      have hqmem : q ∈ execution.componentsAcc.parts := by
        have hp := packAcc_parts_eq execution.packed_eq
        rw [hp] at hmem
        exact hmem
      obtain ⟨index, chosen, run, loops, area, _, _, _, hrun, _, hplace⟩ :=
        (actual_components_parts_geometryX (by rfl) execution.components_eq).2 q hqmem
      have hstraight : (placeComponentExact execution.params
          (componentCandidate execution.graph q.1 index) run 0 execution.measured
          loops).straighten = some ctx0 := by
        have hctxcopy := hctx
        rw [hplace] at hctxcopy
        exact hctxcopy
      unfold placeComponentExact at hstraight
      dsimp only at hstraight
      obtain rfl := Option.some.inj hstraight
      have he0' : run.proper.edges[i]? = some e := he0
      have hmemE : e ∈ run.proper.edges := List.mem_of_getElem? he0'
      obtain ⟨ge, hge, hdeclge⟩ := componentRunX_declInv hrun (normSrc hrun) e hmemE
      have hmap : ((componentCandidate execution.graph q.1 index).edges.map
          (·.decl))[e.original]? = some ge.decl := by
        simp only [List.getElem?_map, hge, Option.map_some]
      have hget : ((componentCandidate execution.graph q.1 index).edges.map
          (·.decl)).getD e.original 0 = ge.decl := by
        simp only [List.getD_eq_getElem?_getD, hmap, Option.getD_some]
      show e.decl = ((componentCandidate execution.graph q.1 index).edges.map
        (·.decl)).getD e.original 0
      exact hdeclge.trans hget.symm
    have hkey : e.decl = key := hm1.trans (hdecl0.symm.trans hdecl)
    exact Or.inr ⟨q, ctx0, ox, oy, i, e, routing, span, hmem, hctx, hoff, he0, hkey, hspan,
      hpts'', hclr⟩

end ExactStraighten
end PipelineImpl
end Layered
end Elegant
