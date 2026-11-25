import Elegant.Layered.SceneBounds
import Elegant.Layered.CoordGraph
import Elegant.Layered.RouteTransport
import Elegant.Layered.SizingFacts

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- A corridor endpoint pair lies on the tail rectangle's bottom and the head rectangle's top. -/
theorem corridor_onBoundary_acc {tailRect headRect : Rect} {x y₀ y₁ : Int}
    (hH : 0 ≤ tailRect.h) (hH' : 0 ≤ headRect.h)
    (hxTail : tailRect.x ≤ x ∧ x ≤ tailRect.x + tailRect.w)
    (hxHead : headRect.x ≤ x ∧ x ≤ headRect.x + headRect.w)
    (hy₀ : y₀ = tailRect.y + tailRect.h) (hy₁ : y₁ = headRect.y) :
    Validator.onBoundary ⟨x, y₀⟩ tailRect ∧ Validator.onBoundary ⟨x, y₁⟩ headRect := by
  constructor
  · unfold Validator.onBoundary
    dsimp only
    omega
  · unfold Validator.onBoundary
    dsimp only
    omega

/-- The same two endpoints after the scene orientation and margin shift. -/
theorem corridor_onBoundary_scene {tailRect headRect : Rect} {x y₀ y₁ : Int}
    {margin : Int} {d : Direction} {h : Int}
    (hb : Validator.onBoundary ⟨x, y₀⟩ tailRect ∧ Validator.onBoundary ⟨x, y₁⟩ headRect) :
    Validator.onBoundary (shiftPoint margin margin (orientPoint d h ⟨x, y₀⟩))
        (shiftRect margin margin (orientRect d h tailRect)) ∧
      Validator.onBoundary (shiftPoint margin margin (orientPoint d h ⟨x, y₁⟩))
        (shiftRect margin margin (orientRect d h headRect)) := by
  have transport : ∀ (p : Point) (r : Rect), Validator.onBoundary p r →
      Validator.onBoundary (shiftPoint margin margin (orientPoint d h p))
        (shiftRect margin margin (orientRect d h r)) := by
    intro p r hp
    cases d with
    | TB =>
      unfold Validator.onBoundary at hp ⊢
      dsimp only [orientPoint, orientRect, shiftPoint, shiftRect] at ⊢
      omega
    | BT =>
      unfold Validator.onBoundary at hp ⊢
      dsimp only [orientPoint, orientRect, shiftPoint, shiftRect] at ⊢
      omega
    | LR =>
      unfold Validator.onBoundary at hp ⊢
      dsimp only [orientPoint, orientRect, shiftPoint, shiftRect] at ⊢
      omega
    | RL =>
      unfold Validator.onBoundary at hp ⊢
      dsimp only [orientPoint, orientRect, shiftPoint, shiftRect] at ⊢
      omega
  exact ⟨transport _ _ hb.1, transport _ _ hb.2⟩

/-- A `Bool` negation that holds forces the original to be false. -/
private theorem bool_of_not_true {b : Bool} (h : (!b) = true) : b = false := by
  cases hb : b with
  | true =>
    simp only [hb] at h
    cases h
   | false => rfl

/-- The straightening port column never lies left of its window. -/
private theorem straightPort_lo {source target lo hi : Int} (hle : lo ≤ hi) :
    lo ≤ straightPort source target lo hi := by
  unfold straightPort
  by_cases h1 : lo ≤ source ∧ source ≤ hi
  · rw [ite_eq_left h1]
    exact h1.1
  · rw [ite_eq_right h1]
    by_cases h2 : lo ≤ target ∧ target ≤ hi
    · rw [ite_eq_left h2]
      exact h2.1
    · rw [ite_eq_right h2]
      omega

/-- The straightening port column never lies right of its window. -/
private theorem straightPort_hi {source target lo hi : Int} (hle : lo ≤ hi) :
    straightPort source target lo hi ≤ hi := by
  unfold straightPort
  by_cases h1 : lo ≤ source ∧ source ≤ hi
  · rw [ite_eq_left h1]
    exact h1.2
  · rw [ite_eq_right h1]
    by_cases h2 : lo ≤ target ∧ target ≤ hi
    · rw [ite_eq_left h2]
      exact h2.2
    · rw [ite_eq_right h2]
      omega

/-- The offset records the straightening context it came from. -/
private theorem straightenOffset_ctx {comp : List Nat} {part : Part} {rects : Array Rect}
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

/-- A successful span names its edge, its eligibility, its declaration, and rises. -/
private theorem straightSpanOf_inv {ctx : StraightenCtx} {routing : Routing} {i : Nat}
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

/-- A span's installed column lies inside its own tail and head rectangles. -/
private theorem straightSpanOf_column_mem {ctx : StraightenCtx} {routing : Routing} {i : Nat}
    {span : StraightSpan} (h : straightSpanOf ctx routing i = .ok (some span)) :
    span.tailRect.x ≤ span.column ∧ span.column ≤ span.tailRect.x + span.tailRect.w ∧
    span.headRect.x ≤ span.column ∧ span.column ≤ span.headRect.x + span.headRect.w := by
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
            obtain ⟨column, hcolNarrow, h⟩ := bind_ok h
            have hs := Option.some.inj (Except.ok.inj h)
            have hcolEq : column = cx + ctx.dx := by
              unfold narrowI32 at hcolNarrow
              by_cases hc : -2147483648 ≤ cx + ctx.dx ∧ cx + ctx.dx ≤ 2147483647
              · rw [ite_eq_left hc] at hcolNarrow
                exact (Except.ok.inj hcolNarrow).symm
              · rw [ite_eq_right hc] at hcolNarrow
                cases hcolNarrow
            simp only [straightGeom] at hgeom
            simp only [StraightGeom.mk.injEq] at hgeom
            obtain ⟨hEtw, hEhw, _, _, hEtl, hEhl, hElo, hEhi, hEcx⟩ := hgeom
            have hle : lo ≤ hi := by omega
            have hSP : straightPort (routing.sourceX.getD i 0) (routing.targetX.getD i 0) lo hi
                = cx := by
              rw [← hElo, ← hEhi]
              exact hEcx
            have hloCx : lo ≤ cx := by
              rw [← hSP]
              exact straightPort_lo hle
            have hhiCx : cx ≤ hi := by
              rw [← hSP]
              exact straightPort_hi hle
            subst hs
            refine ⟨?_, ?_, ?_, ?_⟩
            · show tailLeft + ctx.dx ≤ column
              omega
            · show column ≤ tailLeft + ctx.dx + tw
              omega
            · show headLeft + ctx.dx ≤ column
              omega
            · show column ≤ headLeft + ctx.dx + hw
              omega

/-- A real node behind a straightening lookup is neither dummy nor label nor bordered. -/
private theorem straightRealNode_exists {p : Proper} {v : Nat}
    (h : straightRealNode p v = true) :
    ∃ n, p.nodes[v]? = some n ∧ n.dummy = false ∧ n.label = false ∧ n.node.border = 0 := by
  unfold straightRealNode at h
  cases hv : p.nodes[v]? with
  | none =>
    simp only [hv] at h
    cases h
  | some n =>
    simp only [hv, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hd, hl⟩, hbord⟩ := h
    exact ⟨n, rfl, bool_of_not_true hd, bool_of_not_true hl, hbord⟩

/-- One step installs only old routes or spans. -/
private theorem straightenStep_span {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
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

/-- The edge loop installs only old routes or spans. -/
private theorem straightenFrom_span {ctx : StraightenCtx} {boxes : List (Bool × Rect)} :
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

/-- One component installs only old routes or spans. -/
private theorem straightenComponent_span {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
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

/-- Straightening installs only old routes or spans, with the installing part. -/
private theorem straightenParts_span {boxesOf : StraightenCtx → List Nat → List (Bool × Rect)} {rects : Array Rect} :
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

/-- Folding part rows only rewrites the stored arrays; the part list is unchanged. -/
private theorem foldl_acc_parts (step : Acc → ((List Nat × Part) × Rect) → Acc)
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

/-- Packing shifts stored geometry but keeps every component part. -/
private theorem packAcc_parts_eq {P : Params} {o : Options} {acc out : Acc}
    (h : packAcc P o acc = .ok out) : out.parts = acc.parts := by
  unfold packAcc at h
  obtain ⟨packed, _, h2⟩ := bind_ok h
  have he := Except.ok.inj h2
  subst out
  refine foldl_acc_parts _ ?_ _ _
  intro s q
  rfl

/-- Every proper edge of a successful component run names the component input
edge at its `original` index, which carries the same declaration. -/
private theorem componentRun_declInv {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    DeclInv cg.edges run.proper := by
  obtain ⟨ranks, normalized, labeled, projected, hn, hlabels, hcoordinate,
    _, _, hproxy, hdrop, _⟩ := componentRun_spec hrun
  obtain ⟨hlabelEdges, _, _, _⟩ := Labels.addLabelNodes_metadata hlabels
  have hclean : ∀ e ∈ (titleReservations (sizeProperPorts P labeled)).edges,
      e.synthetic = false := by
    intro e he
    have hedge : (titleReservations (sizeProperPorts P labeled)).edges =
        normalized.edges := hlabelEdges
    rw [hedge] at he
    exact normalize_clean hn e he
  have hprojectedEdges := (proxyWidths_rel hproxy).1
  have hdropEdges : (OrderImpl.dropSynthetic projected).edges =
      (OrderImpl.dropSynthetic
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
          P.clusterBorderW)).edges := by
    show projected.edges.filter (fun e => !e.synthetic) = _
    rw [hprojectedEdges, ← hcoordinate]
    rfl
  have hedgeEq : run.proper.edges = normalized.edges := by
    rw [← hdrop, hdropEdges,
      OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean]
    exact hlabelEdges
  unfold DeclInv
  rw [hedgeEq]
  exact normalize_declInv hn

/-- A route that straightening installed for declaration `key`, with the part,
its context and pack offset, the eligible edge, and the installed span. -/
def Installed (acc : Acc) (key : Nat) (pts : List Point) : Prop :=
  ∃ (q : List Nat × Part) (ctx0 : StraightenCtx) (ox oy : Int) (i : Nat) (e : ProperEdge)
    (span : StraightSpan),
    q ∈ acc.parts ∧ q.2.straighten = some ctx0 ∧
    straightenOffset q.1 q.2 acc.rects = some (ctx0, ox, oy) ∧
    ctx0.proper.edges[i]? = some e ∧ e.decl = key ∧ e.tail ≠ e.head ∧
    ∃ routing, straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing i =
      .ok (some span) ∧ pts = span.points

/-- A real (non-dummy, border-`0`) proper node of a successful component run
lies below the component graph's node count. Real nodes keep their source
index through normalization, label insertion, coordinate materialization,
proxy widths, and synthetic-edge dropping (`NodeKeys`). -/
private theorem installed_proper_below {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hd : nd.dummy = false) (hb : nd.node.border = 0) :
    v < cg.nodes.length := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hkeys : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hdropNodes : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hlenQ : q0.nodes.length = (coordinateGraph P labeled).nodes.length := by
    rw [hcoord]
    exact (proxyWidths_rel hproxy).2.2.1
  have hvq : q0.nodes[v]? = some nd := by
    rw [← hdropNodes]
    exact hv
  have hlt : v < q0.nodes.length := (List.getElem?_eq_some_iff.mp hvq).1
  have hltPc : v < (coordinateGraph P labeled).nodes.length := by
    rw [← hlenQ]
    exact hlt
  obtain ⟨ndpc, hpc⟩ : ∃ ndpc, (coordinateGraph P labeled).nodes[v]? = some ndpc :=
    ⟨_, List.getElem?_eq_getElem hltPc⟩
  have hpc' : run.coordinateProper.nodes[v]? = some ndpc := by
    rw [← hcoord]
    exact hpc
  obtain ⟨nd', hq0', hdEq, hbEq, _⟩ := (proxyWidths_rel hproxy).2.2.2.2.1 v ndpc hpc'
  have hnd' : nd' = nd := Option.some.inj (hq0'.symm.trans hvq)
  subst hnd'
  have hpcDummy : ndpc.dummy = false := by
    rw [← hdEq]
    exact hd
  have hpcBorder : ndpc.node.border = 0 := by
    rw [← hbEq]
    exact hb
  rcases coordinateGraph_lookup P labeled hpc with ⟨m, hm, hdPc, _, _, _⟩ | ⟨_, hbS⟩
    | ⟨_, _, _, _, _, hbT, _⟩
  · rcases hkeys v m hm with ⟨n, hnCg, _, _, _⟩ | ⟨hdLab, _, _⟩
    · exact (List.getElem?_eq_some_iff.mp hnCg).1
    · have hmf : m.dummy = false := by
        rw [← hdPc]
        exact hpcDummy
      rw [hmf] at hdLab
      exact absurd hdLab (by decide)
  · rcases hbS with h | h <;> omega
  · rw [hpcBorder] at hbT
    exact absurd hbT (by decide)

/-- The installing part of an `Installed` witness is an actual placed component,
and its straightening context is that component's context: same proper graph,
coordinates, and part-frame shift. -/
private theorem installed_run_of_mem {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {q : List Nat × Part} {ctx0 : StraightenCtx}
    (hmem : q ∈ execution.componentsAcc.parts)
    (hctx : q.2.straighten = some ctx0) :
    ∃ (index : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int),
      componentRun execution.params
        (componentCandidate execution.graph q.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      q.2 = { placeComponent execution.params
        (componentCandidate execution.graph q.1 index) run 0 execution.measured loops
        with area := area } ∧
      ctx0.proper = run.proper ∧ ctx0.xs = run.xs ∧ ctx0.ys = run.ys ∧
      ctx0.dx = 0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1 index) run execution.measured loops).minX ∧
      ctx0.dy = 0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1 index) run execution.measured loops).minY := by
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hmem
  have hU : (placeComponent execution.params
      (componentCandidate execution.graph q.1 index) run 0 execution.measured loops).straighten
      = some ctx0 := by
    rw [← hctx, hplace]
  unfold placeComponent at hU
  dsimp only at hU
  have hEq := Option.some.inj hU
  have hproper : ctx0.proper = run.proper := congrArg StraightenCtx.proper hEq.symm
  have hxs : ctx0.xs = run.xs := congrArg StraightenCtx.xs hEq.symm
  have hys : ctx0.ys = run.ys := congrArg StraightenCtx.ys hEq.symm
  have hdx : ctx0.dx = 0 - (placeBounds execution.params
    (componentCandidate execution.graph q.1 index) run execution.measured loops).minX :=
    congrArg StraightenCtx.dx hEq.symm
  have hdy : ctx0.dy = 0 - (placeBounds execution.params
    (componentCandidate execution.graph q.1 index) run execution.measured loops).minY :=
    congrArg StraightenCtx.dy hEq.symm
  exact ⟨index, run, loops, area, hrun, hplace, hproper, hxs, hys, hdx, hdy⟩

/-- Guarded single write is an unconditional write (copied from
`ExecutedPortsFacts.guarded_rect_write`; that file is not imported here). -/
private theorem installed_guarded_rect_write (a : Array Rect) (key : Nat) (rect : Rect) :
    (if key < a.size then a.set! key rect else a) = a.set! key rect := by
  by_cases h : key < a.size
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, Array.set!_eq_setIfInBounds]
    simp only [Array.setIfInBounds, h, ↓reduceDIte]

/-- Guarded fold is an unconditional fold (copied from
`ExecutedPortsFacts.guarded_rect_fold`). -/
private theorem installed_guarded_rect_fold (entries : List (Nat × Rect)) (a : Array Rect)
    (transform : Rect → Rect) :
    entries.foldl (fun out entry =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) a =
      entries.foldl (fun out entry => out.set! entry.1 (transform entry.2)) a := by
  have hstep : (fun (out : Array Rect) (entry : Nat × Rect) =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) =
      (fun out entry => out.set! entry.1 (transform entry.2)) := by
    funext out entry
    exact installed_guarded_rect_write out entry.1 (transform entry.2)
  rw [hstep]

/-- The pack fold over `packStep` is a fold of unconditional writes (copied from
`ExecutedPortsFacts.pack_rects_eq_fold`). -/
private theorem installed_pack_rects_eq_fold (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) :
    (pairs.foldl packStep start).rects =
      pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
        (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) start.rects := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    unfold packStep
    dsimp only
    rw [installed_guarded_rect_fold]

/-- The pack fold leaves keys of other parts untouched (copied from
`ExecutedPortsFacts.pack_rects_fold_untouched`). -/
private theorem installed_pack_rects_fold_untouched (pairs : List ((List Nat × Part) × Rect))
    (a : Array Rect) (key : Nat) (fallback : Rect)
    (hnot : ∀ q ∈ pairs, key ∉ q.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD key fallback =
      a.getD key fallback := by
  induction pairs generalizing a with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q' hq' => hnot q' (List.mem_cons_of_mem _ hq'))]
    apply routes_foldl_getD_ne
    intro hm
    obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hm
    exact hnot q List.mem_cons_self (hkey ▸ (List.of_mem_zip hentry).1)

/-- Zip keys are unique when the key list is (copied from
`ExecutedPortsFacts.zip_rect_keys_nodup`). -/
private theorem installed_zip_rect_keys_nodup (keys : List Nat) (rects : List Rect)
    (hn : keys.Nodup) : ((keys.zip rects).map (·.1)).Nodup := by
  induction keys generalizing rects with
  | nil => simp
  | cons key keys ih =>
    cases rects with
    | nil => simp
    | cons rect rects =>
      obtain ⟨hkey, hkeys⟩ := List.nodup_cons.mp hn
      simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih rects hkeys⟩
      intro hm
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hm
      exact hkey (heq ▸ (List.of_mem_zip hentry).1)

/-- The pack fold writes the selected part's entry last (copied from
`ExecutedPortsFacts.pack_rects_fold_selected`). -/
private theorem installed_pack_rects_fold_selected
    (pairs : List ((List Nat × Part) × Rect)) (a : Array Rect)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : pairs[c]? = some q)
    (i key : Nat) (rect fallback : Rect)
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hnodup : q.1.1.Nodup) (hsize : key < a.size)
    (hnot : ∀ q' ∈ pairs.drop (c + 1), key ∉ q'.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD key fallback =
      shiftRect q.2.x q.2.y rect := by
  induction pairs generalizing a c with
  | nil => simp at hselected
  | cons current rest ih =>
    simp only [List.foldl_cons]
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hselected
      subst current
      simp only [List.drop_succ_cons, List.drop_zero] at hnot
      rw [installed_pack_rects_fold_untouched rest _ key fallback hnot]
      exact routes_foldl_getD_mem (shiftRect q.2.x q.2.y) _ a i key rect fallback
        hentry (installed_zip_rect_keys_nodup _ _ hnodup) hsize
    | succ c =>
      simp only [List.getElem?_cons_succ] at hselected
      simp only [List.drop_succ_cons] at hnot
      apply ih _ c hselected
      · rw [routes_foldl_size]
        exact hsize
      · exact hnot

/-- A packed rectangle at a component key is the shifted part rectangle
(copied from `ExecutedPortsFacts.actual_components_packed_rect_value`). -/
private theorem installed_packed_rect_value
    {P : Params} {inp : Input} {o : Options} {graph : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    (hempty : start.parts = [])
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok mid)
    (hpack : packAcc P o mid = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (mid.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {rect : Rect}
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hsize : key < mid.rects.size) (fallback : Rect) :
    out.rects.getD key fallback = shiftRect q.2.x q.2.y rect := by
  obtain ⟨hparts, _⟩ := actual_components_parts hempty hfold
  have hpart : mid.parts[c]? = some q.1 := zip_getElem?_left hselected
  have hmember : q.1 ∈ mid.parts := List.mem_of_getElem? hpart
  have hcomponent : q.1.1 ∈ components graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hmember
  have hnodup : q.1.1.Nodup := components_nodup graph q.1.1 hcomponent
  have hkey : key ∈ q.1.1 := (List.of_mem_zip (List.mem_of_getElem? hentry)).1
  have hnot : ∀ later ∈ (mid.parts.zip packed.boxes).drop (c + 1), key ∉ later.1.1 := by
    intro later hlater
    obtain ⟨j, hcj, hj⟩ := zip_drop_mem_later_getElem? hlater
    have hpartsNodup : (mid.parts.map (·.1)).Nodup := by
      rw [hparts]
      exact components_entries_nodup graph
    obtain ⟨hc, hqc⟩ := List.getElem?_eq_some_iff.mp hpart
    obtain ⟨hjbound, hqj⟩ := List.getElem?_eq_some_iff.mp hj
    have hne : q.1.1 ≠ later.1.1 := by
      have hp := List.pairwise_iff_getElem.mp hpartsNodup
      have hneq := hp c j (by simpa using hc) (by simpa using hjbound) hcj
      simpa only [List.getElem_map, hqc, hqj] using hneq
    have hlaterComponent : later.1.1 ∈ components graph := by
      rw [← hparts]
      exact List.mem_map_of_mem (List.mem_of_getElem? hj)
    exact components_disjoint hcomponent hlaterComponent hne hkey
  unfold packAcc at hpack
  obtain ⟨actualPacked, hactualPacked, hpack⟩ := bind_ok hpack
  have heq : actualPacked = packed := by
    rw [hpacked] at hactualPacked
    exact (Except.ok.inj hactualPacked).symm
  subst actualPacked
  have hout := Except.ok.inj hpack
  subst out
  change ((mid.parts.zip packed.boxes).foldl packStep
    { mid with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects.getD
      key fallback = _
  rw [installed_pack_rects_eq_fold]
  exact installed_pack_rects_fold_selected _ _ c q hselected i key rect fallback hentry hnodup
    hsize hnot

/-- A real (non-dummy, border-`0`) proper node of a successful component run
is the source node at the same index, whose border is `0`: real nodes keep
their source index and border through normalization, label insertion,
coordinate materialization, proxy widths, and synthetic-edge dropping. -/
private theorem installed_proper_cg_node {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hd : nd.dummy = false) (hb : nd.node.border = 0) :
    ∃ n, cg.nodes[v]? = some n ∧ n.border = 0 := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hkeys : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hdropNodes : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hlenQ : q0.nodes.length = (coordinateGraph P labeled).nodes.length := by
    rw [hcoord]
    exact (proxyWidths_rel hproxy).2.2.1
  have hvq : q0.nodes[v]? = some nd := by
    rw [← hdropNodes]
    exact hv
  have hlt : v < q0.nodes.length := (List.getElem?_eq_some_iff.mp hvq).1
  have hltPc : v < (coordinateGraph P labeled).nodes.length := by
    rw [← hlenQ]
    exact hlt
  obtain ⟨ndpc, hpc⟩ : ∃ ndpc, (coordinateGraph P labeled).nodes[v]? = some ndpc :=
    ⟨_, List.getElem?_eq_getElem hltPc⟩
  have hpc' : run.coordinateProper.nodes[v]? = some ndpc := by
    rw [← hcoord]
    exact hpc
  obtain ⟨nd', hq0', hdEq, hbEq, _⟩ := (proxyWidths_rel hproxy).2.2.2.2.1 v ndpc hpc'
  have hnd' : nd' = nd := Option.some.inj (hq0'.symm.trans hvq)
  subst hnd'
  have hpcDummy : ndpc.dummy = false := by
    rw [← hdEq]
    exact hd
  have hpcBorder : ndpc.node.border = 0 := by
    rw [← hbEq]
    exact hb
  rcases coordinateGraph_lookup P labeled hpc with ⟨m, hm, hdPc, hbPc, _, _⟩ | ⟨_, hbS⟩
    | ⟨_, _, _, _, _, hbT, _⟩
  · rcases hkeys v m hm with ⟨n, hnCg, _, hbML, _⟩ | ⟨hdLab, _, _⟩
    · exact ⟨n, hnCg, by rw [← hbML, ← hbPc]; exact hpcBorder⟩
    · have hmf : m.dummy = false := by
        rw [← hdPc]
        exact hpcDummy
      rw [hmf] at hdLab
      exact absurd hdLab (by decide)
  · rcases hbS with h | h <;> omega
  · rw [hpcBorder] at hbT
    exact absurd hbT (by decide)

/-- Every `mapM` success preserves length (copied from
`ComponentCoverage.mapM_ok_length`; that file is not imported here). -/
private theorem installed_mapM_ok_length {err α β : Type} (f : α → Except err β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    change Except.ok [] = Except.ok out at h
    injection h with hout
    subst out
    rfl
  | cons a l ih =>
    intro out h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error err =>
      rw [ha] at h
      change Except.error err = Except.ok out at h
      cases h
    | ok b =>
      cases hxs : l.mapM f with
      | error err =>
        rw [ha, hxs] at h
        change Except.error err = Except.ok out at h
        cases h
      | ok xs =>
        rw [ha, hxs] at h
        change Except.ok (b :: xs) = Except.ok out at h
        injection h with hout
        subst out
        exact congrArg Nat.succ (ih xs hxs)

/-- The execution's measured lines cover every box (copied from
`ComponentCoverage.sceneExecution_lines_len`). -/
private theorem installed_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
        installed_mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- The execution graph's nodes are the marked pre-prepare nodes: the prefix
has the pre-prepare length, which equals the measured lines length. -/
private theorem installed_graph_marked {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∃ N : List Node, execution.graph.nodes =
      Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N ∧ N.length = execution.lines.length := by
  have h := execution.graph_eq
  unfold measuredGraph at h
  obtain ⟨nodes0, hn0, h⟩ := bind_ok h
  obtain ⟨edges, _, h⟩ := bind_ok h
  obtain ⟨mm, _, h⟩ := bind_ok h
  obtain ⟨labels, _, h⟩ := bind_ok h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have hfin := Except.ok.inj h
  refine ⟨nodes, ?_, ?_⟩
  · rw [← hfin]
    rfl
  · have h0 : nodes0.length = execution.lines.length := by
      unfold sizedNodes at hn0
      have h0' := installed_mapM_ok_length _ _ _ hn0
      rwa [List.length_zipIdx] at h0'
    have h1 : nodes.length = nodes0.length := by
      have h1' := installed_mapM_ok_length _ _ _ hnodes
      rwa [List.length_zipIdx, List.length_map] at h1'
    rw [h1]
    exact h0

/-- A plain component-graph node takes the node branch of `frameRect`,
so the frame rectangle is the proper box rectangle. Copy of
`ExecutedPortsFacts.plain_frame_eq_boxRect`; that file imports this one. -/
private theorem installed_plain_frame_eq_boxRect (P : Params) (cg : Graph) (run : Run)
    (v : Nat) (hv : v < run.proper.nodes.length)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    frameRect P cg run v = RouteImpl.boxRect run.proper run.xs run.ys v := by
  have hb : ((cg.nodes.getD v default).border != -2) = true := by
    simp only [bne_iff_ne]
    exact hplain
  unfold frameRect
  dsimp only
  rw [ite_eq_left hb]
  simp only [nodeRect,
    RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.yAt,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
    Option.getD_some, RouteImpl.nodeW, RouteImpl.nodeH]

/-- Tied copy of `installed_markNodes_split` for use before its original. -/
private theorem installed_tied_markNodes_split (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) :
    ∃ marked appended, Compound.markNodes boxes pad titles nodes = marked ++ appended ∧
      marked.length = nodes.length ∧
      (∀ r ∈ appended, r.border = 2) := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp only [List.length_map, List.length_zipIdx]
  · intro r hr
    obtain ⟨qq, hqq, heq⟩ := List.mem_filterMap.mp hr
    cases hrole : qq.1.role == .group with
    | true =>
      simp only [hrole, ↓reduceIte] at heq
      obtain rfl := Option.some.inj heq
      rfl
    | false =>
      simp [hrole] at heq

/-- Tied copy of `installed_key_lt_boxes` for use before its original. -/
private theorem installed_tied_key_lt_boxes {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} {index : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp index)
      labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hd : nd.dummy = false) (hb : nd.node.border = 0)
    (hcomp : comp ∈ components execution.graph)
    {key : Nat} (hkey : comp[v]? = some key) :
    key < inp.boxes.length := by
  obtain ⟨n, hnCg, hnBorder⟩ := installed_proper_cg_node hrun hv hd hb
  have hcgmap : (componentCandidate execution.graph comp index).nodes =
      comp.map fun w => execution.graph.nodes.getD w default := by
    rw [componentCandidate_nodes]
    rfl
  rw [hcgmap, List.getElem?_map, hkey, Option.map_some] at hnCg
  have hfn : execution.graph.nodes.getD key default = n := Option.some.inj hnCg
  have hnB : (execution.graph.nodes.getD key default).border = 0 := by
    rw [hfn]
    exact hnBorder
  obtain ⟨r, hr⟩ := mem_components_eq hcomp
  have hkeyLt : key < execution.graph.nodes.length := by
    have h1 : key ∈ (List.range execution.graph.nodes.length).filter
        (fun w => (componentLab execution.graph)[w]! == r) := by
      rw [← hr]
      exact List.mem_of_getElem? hkey
    exact List.mem_range.mp (List.mem_filter.mp h1).1
  obtain ⟨N, hgraph, hNlen⟩ := installed_graph_marked execution
  have hlines := installed_lines_len execution
  have hN : N.length = inp.boxes.length := by
    rw [hNlen]
    exact hlines
  have hkeyTot : key < (Compound.markNodes
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box)
      execution.params.clusterPad
      (execution.lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * execution.params.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      N).length := by
    rw [← hgraph]
    exact hkeyLt
  obtain ⟨rr, hrGet⟩ : ∃ rr,
      (Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N)[key]? = some rr :=
    ⟨_, List.getElem?_eq_getElem hkeyTot⟩
  have hrn : rr = n := by
    have h1 : (Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N).getD key default = n := by
      have h2 : execution.graph.nodes.getD key default = n := hfn
      rwa [hgraph] at h2
    have h3 : ((Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N)[key]?).getD default = n := h1
    rwa [hrGet] at h3
  obtain ⟨marked, appended, hsplit, hmlen, hbord⟩ :=
    installed_tied_markNodes_split _ _ _ N
  rw [hsplit] at hrGet
  rw [List.getElem?_append] at hrGet
  split at hrGet
  · simp only [hmlen] at *
    rw [← hN]
    assumption
  · have hmem := List.mem_of_getElem? hrGet
    have hb2 := hbord rr hmem
    rw [hrn] at hb2
    rw [hnBorder] at hb2
    exact absurd hb2 (by decide)

/-- Tied copy of `installed_comp_nodes_length`. -/
private theorem installed_tied_comp_nodes_length (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  show (comp.map fun w => g.nodes.getD w default).length = comp.length
  simp

/-- Tied copy of `installed_place_rects_length`. -/
private theorem installed_tied_place_rects_length (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponent
  dsimp only
  simp only [List.length_map, List.length_range]

/-- Tied copy of `installed_pack_fold_rects_size`. -/
private theorem installed_tied_pack_fold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact (packStep_sizes _ _).1

/-- Tied copy of `installed_packAcc_rects_size`. -/
private theorem installed_tied_packAcc_rects_size {P : Params} {o : Options}
    {mid out : Acc} (hpack : packAcc P o mid = .ok out) :
    out.rects.size = mid.rects.size := by
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  have he := Except.ok.inj hpack
  subst out
  change ((mid.parts.zip packed.boxes).foldl packStep
    { mid with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects.size = _
  rw [installed_tied_pack_fold_rects_size]

/-- Tied copy of `installed_fold_rects_size`. -/
private theorem installed_tied_fold_rects_size (P : Params) (inp : Input) (o : Options)
    (graph : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok out →
      out.rects.size = start.rects.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    rw [installed_tied_fold_rects_size P inp o graph labels comps next out hrest]
    exact (layoutComponent_sizes hnext).1.symm
/-- Span-to-rectangle transport with the installing witnesses tied: the packed
rectangles at the part keys share the span column window and meet its top and
bottom edges. Part, keys, bounds and packed rectangles follow
`SceneExecution.installed_edge_keys`; the span is the `Installed` witness. -/
private theorem installed_span_rect_transport_tied {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {q : List Nat × Part} {ctx0 : StraightenCtx} {ox oy : Int} {i : Nat}
    {e : ProperEdge} {span : StraightSpan} {routing : Routing}
    (hmem : q ∈ execution.packedAcc.parts)
    (hctx : q.2.straighten = some ctx0)
    (hoff : straightenOffset q.1 q.2 execution.packedAcc.rects = some (ctx0, ox, oy))
    (he : ctx0.proper.edges[i]? = some e)
    (hspan : straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
      routing i = .ok (some span)) :
    ∃ (tailKey headKey : Nat) (tailRect headRect : Rect),
      e.tail < q.1.length ∧ e.head < q.1.length ∧
      q.1[e.tail]? = some tailKey ∧ q.1[e.head]? = some headKey ∧
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect ∧
      0 ≤ tailRect.h ∧ 0 ≤ headRect.h ∧
      tailRect.x = span.tailRect.x ∧ tailRect.w = span.tailRect.w ∧
      headRect.x = span.headRect.x ∧ headRect.w = span.headRect.w ∧
      span.top = tailRect.y + tailRect.h ∧ span.bottom = headRect.y := by
  have hpartsEq := packAcc_parts_eq execution.packed_eq
  have hmemC : q ∈ execution.componentsAcc.parts := by
    rwa [hpartsEq] at hmem
  obtain ⟨index, run, loops, area, hrun, hplace, hproper, hxs, hys, hdx, hdy⟩ :=
    installed_run_of_mem execution hmemC hctx
  obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_inv hspan
  have he'2 : ctx0.proper.edges[i]? = some e' := he'
  have heq : e' = e := Option.some.inj (he'2.symm.trans he)
  rw [heq] at he' helig
  have helig0 : straightEdgeEligible ctx0 routing i e = true := helig
  unfold straightEdgeEligible at helig0
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig0
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := helig0
  obtain ⟨tailNode, hvt0, htd, htl, htb⟩ := straightRealNode_exists hTail
  obtain ⟨headNode, hvh0, hhd, hhl, hhb⟩ := straightRealNode_exists hHead
  have hvt : run.proper.nodes[e.tail]? = some tailNode := by
    rw [← hproper]
    exact hvt0
  have hvh : run.proper.nodes[e.head]? = some headNode := by
    rw [← hproper]
    exact hvh0
  have htailLtCg : e.tail < (componentCandidate execution.graph q.1 index).nodes.length :=
    installed_proper_below hrun hvt htd htb
  have hheadLtCg : e.head < (componentCandidate execution.graph q.1 index).nodes.length :=
    installed_proper_below hrun hvh hhd hhb
  have hclen : (componentCandidate execution.graph q.1 index).nodes.length = q.1.length :=
    installed_tied_comp_nodes_length _ _ _
  have htailLt : e.tail < q.1.length := by
    rw [← hclen]
    exact htailLtCg
  have hheadLt : e.head < q.1.length := by
    rw [← hclen]
    exact hheadLtCg
  obtain ⟨tailKey, htk⟩ : ∃ k, q.1[e.tail]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨htailLt, rfl⟩⟩
  obtain ⟨headKey, hhk⟩ : ∃ k, q.1[e.head]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨hheadLt, rfl⟩⟩
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hparts, _⟩ := actual_components_parts hempty execution.components_eq
  have hmember : (q.1, q.2) ∈ execution.componentsAcc.parts := hmemC
  have hcomp : q.1 ∈ components execution.graph := by
    have h1 : q.1 ∈ execution.componentsAcc.parts.map (·.1) :=
      List.mem_map_of_mem hmember
    rwa [hparts] at h1
  have hmidSize : execution.componentsAcc.rects.size = inp.boxes.length := by
    have hsz := installed_tied_fold_rects_size execution.params inp o execution.graph
      execution.measured (components execution.graph) _ _ execution.components_eq
    rw [hsz]
    exact Array.size_replicate
  have hsizeT_mid : tailKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact installed_tied_key_lt_boxes execution hrun hvt htd htb hcomp htk
  have hsizeH_mid : headKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact installed_tied_key_lt_boxes execution hrun hvh hhd hhb hcomp hhk
  have hsizeT : tailKey < execution.packedAcc.rects.size := by
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_tied_packAcc_rects_size execution.packed_eq).symm
    have h1 : tailKey < inp.boxes.length :=
      installed_tied_key_lt_boxes execution hrun hvt htd htb hcomp htk
    omega
  have hsizeH : headKey < execution.packedAcc.rects.size := by
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_tied_packAcc_rects_size execution.packed_eq).symm
    have h1 : headKey < inp.boxes.length :=
      installed_tied_key_lt_boxes execution hrun hvh hhd hhb hcomp hhk
    omega
  have hpackEq := execution.packed_eq
  unfold packAcc at hpackEq
  obtain ⟨packed, hpacked, hprest⟩ := bind_ok hpackEq
  have hplen : execution.componentsAcc.parts.length = packed.boxes.length := by
    have hcount := Pack.pack_count hpacked
    rw [hcount, List.length_map]
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hmemC
  have hcLt : c < packed.boxes.length := by
    have h1 : c < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hc).1
    omega
  have hbox : packed.boxes[c]? = some packed.boxes[c] :=
    List.getElem?_eq_some_iff.mpr ⟨hcLt, rfl⟩
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (q, packed.boxes[c]) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hbox⟩
  have hrectsLen : q.2.rects.length = q.1.length := by
    have h1 := installed_tied_place_rects_length execution.params
      (componentCandidate execution.graph q.1 index) run execution.measured loops
    have h2 := installed_tied_comp_nodes_length execution.graph q.1 index
    rw [hplace, h1]
    exact h2
  have hRt : e.tail < q.2.rects.length := by
    rw [hrectsLen]
    exact htailLt
  have hRh : e.head < q.2.rects.length := by
    rw [hrectsLen]
    exact hheadLt
  obtain ⟨rectT, hrT⟩ : ∃ r, q.2.rects[e.tail]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRt⟩
  obtain ⟨rectH, hrH⟩ : ∃ r, q.2.rects[e.head]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRh⟩
  have hentryT : (q.1.zip q.2.rects)[e.tail]? = some (tailKey, rectT) :=
    List.getElem?_zip_eq_some.mpr ⟨htk, hrT⟩
  have hentryH : (q.1.zip q.2.rects)[e.head]? = some (headKey, rectH) :=
    List.getElem?_zip_eq_some.mpr ⟨hhk, hrH⟩
  have hvalT := installed_packed_rect_value hempty execution.components_eq execution.packed_eq
    packed hpacked hselected hentryT hsizeT_mid default
  have hvalH := installed_packed_rect_value hempty execution.components_eq execution.packed_eq
    packed hpacked hselected hentryH hsizeH_mid default
  have hlookT : execution.packedAcc.rects[tailKey]?
      = some (shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT) := by
    have hneT : execution.packedAcc.rects[tailKey]? ≠ none := by
      intro hcon
      have hle := Array.getElem?_eq_none_iff.mp hcon
      omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hneT
    have h2 : ((execution.packedAcc.rects[tailKey]?).getD default)
        = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalT
    have h3 : r = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  have hlookH : execution.packedAcc.rects[headKey]?
      = some (shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH) := by
    have hneH : execution.packedAcc.rects[headKey]? ≠ none := by
      intro hcon
      have hle := Array.getElem?_eq_none_iff.mp hcon
      omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hneH
    have h2 : ((execution.packedAcc.rects[headKey]?).getD default)
        = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalH
    have h3 : r = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  have hdims := componentRun_dims_nonneg hrun
  let ctxS : StraightenCtx := { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
  have hspanS : straightSpanOf ctxS routing i = .ok (some span) := hspan
  have hspanUnfold := hspanS
  unfold straightSpanOf at hspanUnfold
  cases heS : ctxS.proper.edges[i]? with
  | none =>
    simp only [heS] at hspanUnfold
    cases hspanUnfold
  | some eS =>
    simp only [heS] at hspanUnfold
    have heQ : ctx0.proper.edges[i]? = some eS := heS
    have heSEq : eS = e := Option.some.inj (heQ.symm.trans he)
    rw [heSEq] at hspanUnfold heS
    cases helS : !straightEdgeEligible ctxS routing i e with
    | true =>
      simp only [helS] at hspanUnfold
      cases hspanUnfold
    | false =>
      simp only [helS] at hspanUnfold
      cases hgeom : straightGeom ctxS routing i e with
      | mk tw hw th hh tailLeft headLeft lo hi cx =>
        simp only [hgeom] at hspanUnfold
        by_cases hlo : lo > hi
        · rw [ite_eq_left hlo] at hspanUnfold
          cases hspanUnfold
        · rw [ite_eq_right hlo] at hspanUnfold
          obtain ⟨pin, hpinN, hrest1⟩ := bind_ok hspanUnfold
          obtain ⟨top, htopN, hrest2⟩ := bind_ok hrest1
          obtain ⟨bottom, hbotN, hrest3⟩ := bind_ok hrest2
          by_cases hge : top ≥ bottom
          · rw [ite_eq_left hge] at hrest3
            cases hrest3
          · rw [ite_eq_right hge] at hrest3
            obtain ⟨column, hcolN, hfin⟩ := bind_ok hrest3
            have hsEq := Option.some.inj (Except.ok.inj hfin)
            have hpinEq : pin = cx := by
              unfold narrowI32 at hpinN
              by_cases hc : -2147483648 ≤ cx ∧ cx ≤ 2147483647
              · rw [ite_eq_left hc] at hpinN
                exact (Except.ok.inj hpinN).symm
              · rw [ite_eq_right hc] at hpinN
                cases hpinN
            have htopEq : top = ctx0.ys.getD e.tail 0 + th + (ctx0.dy + oy) := by
              unfold narrowI32 at htopN
              have hctxYs : ctxS.ys.getD e.tail 0 = ctx0.ys.getD e.tail 0 := rfl
              have hctxDy : ctxS.dy = ctx0.dy + oy := rfl
              by_cases hc : -2147483648 ≤ ctx0.ys.getD e.tail 0 + th +
                  (ctx0.dy + oy) ∧ ctx0.ys.getD e.tail 0 + th + (ctx0.dy + oy) ≤ 2147483647
              · have hc' : -2147483648 ≤ ctxS.ys.getD e.tail 0 + th + ctxS.dy ∧
                  ctxS.ys.getD e.tail 0 + th + ctxS.dy ≤ 2147483647 := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_left hc'] at htopN
                have htop0 := (Except.ok.inj htopN).symm
                rwa [hctxYs, hctxDy] at htop0
              · have hc' : ¬ (-2147483648 ≤ ctxS.ys.getD e.tail 0 + th + ctxS.dy ∧
                  ctxS.ys.getD e.tail 0 + th + ctxS.dy ≤ 2147483647) := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_right hc'] at htopN
                cases htopN
            have hbotEq : bottom = ctx0.ys.getD e.head 0 + (ctx0.dy + oy) := by
              unfold narrowI32 at hbotN
              have hctxYs : ctxS.ys.getD e.head 0 = ctx0.ys.getD e.head 0 := rfl
              have hctxDy : ctxS.dy = ctx0.dy + oy := rfl
              by_cases hc : -2147483648 ≤ ctx0.ys.getD e.head 0 +
                  (ctx0.dy + oy) ∧ ctx0.ys.getD e.head 0 + (ctx0.dy + oy) ≤ 2147483647
              · have hc' : -2147483648 ≤ ctxS.ys.getD e.head 0 + ctxS.dy ∧
                  ctxS.ys.getD e.head 0 + ctxS.dy ≤ 2147483647 := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_left hc'] at hbotN
                have hbot0 := (Except.ok.inj hbotN).symm
                rwa [hctxYs, hctxDy] at hbot0
              · have hc' : ¬ (-2147483648 ≤ ctxS.ys.getD e.head 0 + ctxS.dy ∧
                  ctxS.ys.getD e.head 0 + ctxS.dy ≤ 2147483647) := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_right hc'] at hbotN
                cases hbotN
            have hcolEq : column = cx + (ctx0.dx + ox) := by
              unfold narrowI32 at hcolN
              have hctxDx : ctxS.dx = ctx0.dx + ox := rfl
              by_cases hc : -2147483648 ≤ cx + (ctx0.dx + ox) ∧
                  cx + (ctx0.dx + ox) ≤ 2147483647
              · have hc' : -2147483648 ≤ cx + ctxS.dx ∧ cx + ctxS.dx ≤ 2147483647 := by
                  rwa [hctxDx]
                rw [ite_eq_left hc'] at hcolN
                have hcol0 := (Except.ok.inj hcolN).symm
                rwa [hctxDx] at hcol0
              · have hc' : ¬ (-2147483648 ≤ cx + ctxS.dx ∧ cx + ctxS.dx ≤ 2147483647) := by
                  rwa [hctxDx]
                rw [ite_eq_right hc'] at hcolN
                cases hcolN
            subst hsEq
            simp only [straightGeom] at hgeom
            simp only [StraightGeom.mk.injEq] at hgeom
            obtain ⟨hEtw, hEhw, hEth, hEhh, hEtl, hEhl, _, _, _⟩ := hgeom
            have hxsT : ctx0.xs.getD e.tail 0 = run.xs.getD e.tail 0 := by
              rw [hxs]
            have hxsH : ctx0.xs.getD e.head 0 = run.xs.getD e.head 0 := by
              rw [hxs]
            have hysT : ctx0.ys.getD e.tail 0 = run.ys.getD e.tail 0 := by
              rw [hys]
            have hysH : ctx0.ys.getD e.head 0 = run.ys.getD e.head 0 := by
              rw [hys]
            have hproperEq : ctx0.proper = run.proper := hproper
            have htwEq : tw = tailNode.node.w := by
              have htw0 : tw = RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail := by
                rw [← hEtw]
                rfl
              have htw1 : RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail =
                  RouteImpl.nodeW ctx0.proper e.tail := rfl
              rw [htw0, htw1, hproperEq]
              simp only [RouteImpl.nodeW, hvt]
            have hhwEq : hw = headNode.node.w := by
              have hhw0 : hw = RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head := by
                rw [← hEhw]
                rfl
              have hhw1 : RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head =
                  RouteImpl.nodeW ctx0.proper e.head := rfl
              rw [hhw0, hhw1, hproperEq]
              simp only [RouteImpl.nodeW, hvh]
            have hthEq : th = tailNode.node.h := by
              have hth0 : th = RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail := by
                rw [← hEth]
                rfl
              have hth1 : RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail =
                  RouteImpl.nodeH ctx0.proper e.tail := rfl
              rw [hth0, hth1, hproperEq]
              simp only [RouteImpl.nodeH, hvt]
            have hhhEq : hh = headNode.node.h := by
              have hhh0 : hh = RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head := by
                rw [← hEhh]
                rfl
              have hhh1 : RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head =
                  RouteImpl.nodeH ctx0.proper e.head := rfl
              rw [hhh0, hhh1, hproperEq]
              simp only [RouteImpl.nodeH, hvh]
            have hxsEqT : ctxS.xs.getD e.tail 0 = ctx0.xs.getD e.tail 0 := rfl
            have hxsEqH : ctxS.xs.getD e.head 0 = ctx0.xs.getD e.head 0 := rfl
            have htlEq : tailLeft = ctx0.xs.getD e.tail 0 - tw / 2 := by
              rw [← hEtl, hxsEqT, hEtw]
            have hhlEq : headLeft = ctx0.xs.getD e.head 0 - hw / 2 := by
              rw [← hEhl, hxsEqH, hEhw]
            have htailDims := hdims e.tail tailNode hvt
            have hheadDims := hdims e.head headNode hvh
            have hthNonneg : 0 ≤ th := by
              rw [hthEq]
              exact htailDims.2
            have hhhNonneg : 0 ≤ hh := by
              rw [hhhEq]
              exact hheadDims.2
            have htwNonneg : 0 ≤ tw := by
              rw [htwEq]
              exact htailDims.1
            have hwNonneg : 0 ≤ hw := by
              rw [hhwEq]
              exact hheadDims.1
            have hvtLt : e.tail < run.proper.nodes.length :=
              (List.getElem?_eq_some_iff.mp hvt).1
            have hvhLt : e.head < run.proper.nodes.length :=
              (List.getElem?_eq_some_iff.mp hvh).1
            obtain ⟨cgTail, hcgTail, hcgTailB⟩ :=
              installed_proper_cg_node hrun hvt htd htb
            obtain ⟨cgHead, hcgHead, hcgHeadB⟩ :=
              installed_proper_cg_node hrun hvh hhd hhb
            have hplainT : ((componentCandidate execution.graph q.1 index).nodes.getD
                e.tail default).border ≠ -2 := by
              have hget : (componentCandidate execution.graph q.1 index).nodes.getD
                  e.tail default = cgTail := by
                simp only [List.getD_eq_getElem?_getD, hcgTail, Option.getD_some]
              rw [hget, hcgTailB]
              omega
            have hplainH : ((componentCandidate execution.graph q.1 index).nodes.getD
                e.head default).border ≠ -2 := by
              have hget : (componentCandidate execution.graph q.1 index).nodes.getD
                  e.head default = cgHead := by
                simp only [List.getD_eq_getElem?_getD, hcgHead, Option.getD_some]
              rw [hget, hcgHeadB]
              omega
            have hframeT : frameRect execution.params
                (componentCandidate execution.graph q.1 index) run e.tail =
                RouteImpl.boxRect run.proper run.xs run.ys e.tail :=
              installed_plain_frame_eq_boxRect _ _ _ _ hvtLt hplainT
            have hframeH : frameRect execution.params
                (componentCandidate execution.graph q.1 index) run e.head =
                RouteImpl.boxRect run.proper run.xs run.ys e.head :=
              installed_plain_frame_eq_boxRect _ _ _ _ hvhLt hplainH
            have hrectTEq : rectT = shiftRect ctx0.dx ctx0.dy
                (frameRect execution.params
                  (componentCandidate execution.graph q.1 index) run e.tail) := by
              have hlookup : q.2.rects[e.tail]? = some (shiftRect ctx0.dx ctx0.dy
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1 index) run e.tail)) := by
                rw [hplace]
                show (placeComponent execution.params
                  (componentCandidate execution.graph q.1 index) run 0
                  execution.measured loops).rects[e.tail]? = _
                unfold placeComponent
                dsimp only
                simp only [List.getElem?_map, List.getElem?_range htailLtCg,
                  Option.map_some]
                unfold placeBounds at hdx hdy
                rw [hdx, hdy]
              rw [hlookup] at hrT
              exact (Option.some.inj hrT).symm
            have hrectHEq : rectH = shiftRect ctx0.dx ctx0.dy
                (frameRect execution.params
                  (componentCandidate execution.graph q.1 index) run e.head) := by
              have hlookup : q.2.rects[e.head]? = some (shiftRect ctx0.dx ctx0.dy
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1 index) run e.head)) := by
                rw [hplace]
                show (placeComponent execution.params
                  (componentCandidate execution.graph q.1 index) run 0
                  execution.measured loops).rects[e.head]? = _
                unfold placeComponent
                dsimp only
                simp only [List.getElem?_map, List.getElem?_range hheadLtCg,
                  Option.map_some]
                unfold placeBounds at hdx hdy
                rw [hdx, hdy]
              rw [hlookup] at hrH
              exact (Option.some.inj hrH).symm
            obtain ⟨v0, r0, base0, rest0, hzip0, hstraight0, hbase0, hox0, hoy0⟩ :
                ∃ (v : Nat) (r : Rect) (base : Rect) (rest : List (Nat × Rect)),
                  q.1.zip q.2.rects = (v, r) :: rest ∧
                  q.2.straighten = some ctx0 ∧
                  execution.packedAcc.rects[v]? = some base ∧
                  ox = base.x - r.x ∧ oy = base.y - r.y := by
              unfold straightenOffset at hoff
              cases h1off : q.2.straighten with
              | none =>
                simp only [h1off] at hoff
                cases hoff
              | some cc =>
                cases h2off : q.1.zip q.2.rects with
                | nil =>
                  simp only [h1off, h2off] at hoff
                  cases hoff
                | cons pr rest =>
                  cases pr with
                  | mk v r =>
                    cases h3off : execution.packedAcc.rects[v]? with
                    | none =>
                      simp only [h1off, h2off, h3off] at hoff
                      cases hoff
                    | some base =>
                      simp only [h1off, h2off, h3off] at hoff
                      have heq := Option.some.inj hoff
                      simp only [Prod.mk.injEq] at heq
                      obtain ⟨hctxEq, hoxEq, hoyEq⟩ := heq
                      exact Exists.intro v (Exists.intro r (Exists.intro base
                        (Exists.intro rest ⟨rfl, congrArg some hctxEq, h3off,
                          hoxEq.symm, hoyEq.symm⟩)))
            have hv0Packed : v0 < execution.packedAcc.rects.size := by
              obtain ⟨h, _⟩ := Array.getElem?_eq_some_iff.mp hbase0
              exact h
            have hv0Mid : v0 < execution.componentsAcc.rects.size := by
              have heqSize := installed_tied_packAcc_rects_size execution.packed_eq
              omega
            have hentry0 : (q.1.zip q.2.rects)[0]? = some (v0, r0) := by
              simp [hzip0]
            have hval0 := installed_packed_rect_value hempty execution.components_eq
              execution.packed_eq packed hpacked hselected hentry0 hv0Mid default
            have hlook0 : execution.packedAcc.rects[v0]?
                = some (shiftRect (q, packed.boxes[c]).2.x
                  (q, packed.boxes[c]).2.y r0) := by
              have hne0 : execution.packedAcc.rects[v0]? ≠ none := by
                intro hcon
                have hle := Array.getElem?_eq_none_iff.mp hcon
                omega
              obtain ⟨rr, hrr⟩ := Option.ne_none_iff_exists'.mp hne0
              have h22 : ((execution.packedAcc.rects[v0]?).getD default)
                  = shiftRect (q, packed.boxes[c]).2.x
                    (q, packed.boxes[c]).2.y r0 := by
                rw [← Array.getD_eq_getD_getElem?]
                exact hval0
              have h33 : rr = shiftRect (q, packed.boxes[c]).2.x
                  (q, packed.boxes[c]).2.y r0 := by
                rw [hrr] at h22
                simpa using h22
              rwa [h33] at hrr
            have hbaseEq : base0 = shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y r0 :=
              Option.some.inj (hbase0.symm.trans hlook0)
            have hbxEq : base0.x = r0.x + (packed.boxes[c]).x := by
              have hbb : base0 = shiftRect (packed.boxes[c]).x
                  (packed.boxes[c]).y r0 := by
                have : (q, packed.boxes[c]).2.x = (packed.boxes[c]).x := rfl
                have : (q, packed.boxes[c]).2.y = (packed.boxes[c]).y := rfl
                rwa [this, this] at hbaseEq
              rw [hbb]
              rfl
            have hbyEq : base0.y = r0.y + (packed.boxes[c]).y := by
              have hbb : base0 = shiftRect (packed.boxes[c]).x
                  (packed.boxes[c]).y r0 := by
                have : (q, packed.boxes[c]).2.x = (packed.boxes[c]).x := rfl
                have : (q, packed.boxes[c]).2.y = (packed.boxes[c]).y := rfl
                rwa [this, this] at hbaseEq
              rw [hbb]
              rfl
            have hoxBx : ox = (packed.boxes[c]).x := by omega
            have hoyBy : oy = (packed.boxes[c]).y := by omega
            have hboxX : (q, packed.boxes[c]).2.x = (packed.boxes[c]).x := rfl
            have hboxY : (q, packed.boxes[c]).2.y = (packed.boxes[c]).y := rfl
            have hfdivT : Int.fdiv tailNode.node.w 2 = tailNode.node.w / 2 :=
              Int.fdiv_eq_ediv_of_nonneg _ (by decide)
            have hfdivH : Int.fdiv headNode.node.w 2 = headNode.node.w / 2 :=
              Int.fdiv_eq_ediv_of_nonneg _ (by decide)
            have htailRectX : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).x =
                tailLeft + (ctx0.dx + ox) := by
              rw [hrectTEq, hframeT, htlEq, htwEq, hxsT, hoxBx, hboxX]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.xAt,
                RouteImpl.nodeW, hvt, hfdivT]
              omega
            have htailRectW : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).w = tw := by
              rw [hrectTEq, hframeT, htwEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeW, hvt]
            have hheadRectX : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).x =
                headLeft + (ctx0.dx + ox) := by
              rw [hrectHEq, hframeH, hhlEq, hhwEq, hxsH, hoxBx, hboxX]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.xAt,
                RouteImpl.nodeW, hvh, hfdivH]
              omega
            have hheadRectW : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).w = hw := by
              rw [hrectHEq, hframeH, hhwEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeW, hvh]
            have htailRectY : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).y =
                ctx0.ys.getD e.tail 0 + (ctx0.dy + oy) := by
              rw [hrectTEq, hframeT, hysT, hoyBy, hboxY]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.yAt]
              omega
            have htailRectH : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).h = th := by
              rw [hrectTEq, hframeT, hthEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeH, hvt]
            have hheadRectY : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).y =
                ctx0.ys.getD e.head 0 + (ctx0.dy + oy) := by
              rw [hrectHEq, hframeH, hysH, hoyBy, hboxY]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.yAt]
              omega
            have hheadRectH : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).h = hh := by
              rw [hrectHEq, hframeH, hhhEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeH, hvh]
            have htopEq' : top = (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).y +
                (shiftRect (q, packed.boxes[c]).2.x
                  (q, packed.boxes[c]).2.y rectT).h := by
              rw [htopEq, htailRectY, htailRectH]
              omega
            have hbotEq' : bottom = (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).y := by
              rw [hbotEq, hheadRectY]
            have hfinalTh : 0 ≤ (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).h := by
              rw [htailRectH]
              exact hthNonneg
            have hfinalHh : 0 ≤ (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).h := by
              rw [hheadRectH]
              exact hhhNonneg
            have hfinalTx : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).x =
                tailLeft + (ctx0.dx + ox) := htailRectX
            have hfinalTw : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).w = tw := htailRectW
            have hfinalHx : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).x =
                headLeft + (ctx0.dx + ox) := hheadRectX
            have hfinalHw : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).w = hw := hheadRectW
            exact ⟨tailKey, headKey, _, _, htailLt, hheadLt, htk, hhk,
              hlookT, hlookH, hfinalTh, hfinalHh, hfinalTx, hfinalTw,
              hfinalHx, hfinalHw, htopEq', hbotEq'⟩

/-- The packed rectangles behind an installed route: the part, its context and
pack offset, the proper edge with real endpoints, the part keys, and the packed
rectangles sharing the span window and meeting its top and bottom edges. -/
private theorem installed_packed_rect_transport {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts) :
    ∃ (q : List Nat × Part) (ctx0 : StraightenCtx) (ox oy : Int) (i : Nat)
      (e : ProperEdge) (span : StraightSpan)
      (tailKey headKey : Nat) (tailRect headRect : Rect),
      q ∈ execution.packedAcc.parts ∧ q.2.straighten = some ctx0 ∧
      straightenOffset q.1 q.2 execution.packedAcc.rects = some (ctx0, ox, oy) ∧
      ctx0.proper.edges[i]? = some e ∧ e.decl = key ∧ e.tail ≠ e.head ∧
      e.tail < q.1.length ∧ e.head < q.1.length ∧
      q.1[e.tail]? = some tailKey ∧ q.1[e.head]? = some headKey ∧
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect ∧
      0 ≤ tailRect.h ∧ 0 ≤ headRect.h ∧
      tailRect.x = span.tailRect.x ∧ tailRect.w = span.tailRect.w ∧
      headRect.x = span.headRect.x ∧ headRect.w = span.headRect.w ∧
      span.top = tailRect.y + tailRect.h ∧ span.bottom = headRect.y := by
  obtain ⟨q, ctx0, ox, oy, i, e, span, hmem, hctx, hoff, he, hkey, hne,
    routing, hspan, _⟩ := hinst
  obtain ⟨tailKey, headKey, tailRect, headRect, hbt, hbh, htk, hhk,
    hlookT, hlookH, hth, hhh, htx, htw, hhx, hhw, htop, hbot⟩ :=
    installed_span_rect_transport_tied execution hmem hctx hoff he hspan
  exact ⟨q, ctx0, ox, oy, i, e, span, tailKey, headKey, tailRect, headRect,
    hmem, hctx, hoff, he, hkey, hne, hbt, hbh, htk, hhk, hlookT, hlookH,
    hth, hhh, htx, htw, hhx, hhw, htop, hbot⟩


/-- One step installs only old routes or spans that passed the obstacle check. -/
private theorem straightenStep_span_clear {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
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

/-- The edge loop installs only old routes or spans that passed the obstacle check. -/
private theorem straightenFrom_span_clear {ctx : StraightenCtx} {boxes : List (Bool × Rect)} :
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

/-- One component installs only old routes or spans that passed the obstacle check. -/
private theorem straightenComponent_span_clear {ctx : StraightenCtx} {boxes : List (Bool × Rect)}
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

/-- Straightening installs only old routes or spans that passed the obstacle check. -/
private theorem straightenParts_span_clear {boxesOf : StraightenCtx → List Nat → List (Bool × Rect)} {rects : Array Rect} :
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

/-- Every route of the straightened accumulator is the packed route or an installed
corridor that passed the obstacle check on the part boxes. -/
theorem SceneExecution.route_cases_clear {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat} {pts : List Point}
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
  cases straightenParts_span_clear execution.packedAcc.parts execution.packedAcc.routes routes h1 key pts
    hpts' with
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
      obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
        execution.actual_component_sizing hqmem
      have hstraight : (placeComponent execution.params
          (componentCandidate execution.graph q.1 index) run 0 execution.measured
          loops).straighten = some ctx0 := by
        have hctxcopy := hctx
        rw [hplace] at hctxcopy
        exact hctxcopy
      unfold placeComponent at hstraight
      dsimp only at hstraight
      obtain rfl := Option.some.inj hstraight
      have he0' : run.proper.edges[i]? = some e := he0
      have hmemE : e ∈ run.proper.edges := List.mem_of_getElem? he0'
      obtain ⟨ge, hge, hdeclge⟩ := componentRun_declInv hrun e hmemE
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
    have hclr' : straightStepClear (straightenPartBoxes inp execution.packedAcc ctx0 q.1) span.tailRect
        span.headRect span.top span.bottom span.column = true := hclr
    exact Or.inr ⟨q, ctx0, ox, oy, i, e, routing, span, hmem, hctx, hoff, he0, hkey, hspan,
      hpts'', hclr'⟩

/-- Every route of the straightened accumulator is the packed route or was installed. -/
theorem SceneExecution.route_cases {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat} {pts : List Point}
    (hpts : execution.straightAcc.routes[key]? = some pts) :
    execution.packedAcc.routes[key]? = some pts ∨ Installed execution.packedAcc key pts := by
  obtain ⟨routes, h1, h2⟩ := bind_ok execution.straight_eq
  have heq := Except.ok.inj h2
  have hst : routes = execution.straightAcc.routes := congrArg Acc.routes heq
  simp only [straightenRoutes] at h1
  have hpts' : routes[key]? = some pts := by
    rw [hst]
    exact hpts
  cases straightenParts_span execution.packedAcc.parts execution.packedAcc.routes routes h1 key pts
    hpts' with
  | inl hold => exact Or.inl hold
  | inr hw =>
    obtain ⟨q, ctx0, ox, oy, routing, i, span, hmem, hctx, hoff, hspan, hdecl, hpts''⟩ := hw
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
    -- Missing fact (M1): the proper edge's declaration equals the part's decl table
    -- at its original index. Concrete bridge: `DeclInv` (`PipelineFacts.lean:1374`)
    -- via `normalize_declInv` (`PipelineFacts.lean:1415`), replayed for `run.proper`
    -- as in `componentRun_facts` (`PipelineFacts.lean:1706`), with the run taken from
    -- `SceneExecution.actual_component_sizing` (`SceneBounds.lean:1157`) and
    -- `placeComponent` (`Pipeline.lean:536-541`) setting
    -- `decls := (componentCandidate …).edges.map (·.decl)`; `CovEdge`
    -- (`Normalize.lean:310`) is the same fact in covering form.
    have hm1 : e.decl = ctx0.decls.getD e.original 0 := by
      have hqmem : q ∈ execution.componentsAcc.parts := by
        have hp := packAcc_parts_eq execution.packed_eq
        rw [hp] at hmem
        exact hmem
      obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
        execution.actual_component_sizing hqmem
      have hstraight : (placeComponent execution.params
          (componentCandidate execution.graph q.1 index) run 0 execution.measured
          loops).straighten = some ctx0 := by
        have hctxcopy := hctx
        rw [hplace] at hctxcopy
        exact hctxcopy
      unfold placeComponent at hstraight
      dsimp only at hstraight
      obtain rfl := Option.some.inj hstraight
      have he0' : run.proper.edges[i]? = some e := he0
      have hmemE : e ∈ run.proper.edges := List.mem_of_getElem? he0'
      obtain ⟨ge, hge, hdeclge⟩ := componentRun_declInv hrun e hmemE
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
    exact Or.inr ⟨q, ctx0, ox, oy, i, e, span, hmem, hctx, hoff, he0, hkey, hne, routing, hspan,
      hpts''⟩

/-- An installed route joins two real nodes: no dummy, no label node, no border. -/
theorem SceneExecution.installed_real_nodes {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat} {pts : List Point}
    (hinst : Installed execution.packedAcc key pts) :
    ∃ tailNode headNode : ProperNode,
      tailNode.dummy = false ∧ headNode.dummy = false ∧
      tailNode.label = false ∧ headNode.label = false ∧
      tailNode.node.border = 0 ∧ headNode.node.border = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hspan, _⟩ := hinst
  obtain ⟨_, _, helig, _, _⟩ := straightSpanOf_inv hspan
  unfold straightEdgeEligible at helig
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := helig
  obtain ⟨tailNode, _, htd, htl, htb⟩ := straightRealNode_exists hTail
  obtain ⟨headNode, _, hhd, hhl, hhb⟩ := straightRealNode_exists hHead
  exact ⟨tailNode, headNode, htd, hhd, htl, hhl, htb, hhb⟩

/-- An installed route is a vertical segment from the packed tail rectangle's bottom
edge to the packed head rectangle's top edge, with its column inside both. -/
theorem SceneExecution.installed_endpoints {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat} {pts : List Point}
    (hinst : Installed execution.packedAcc key pts) :
    ∃ (x y₀ y₁ : Int) (tailKey headKey : Nat) (tailRect headRect : Rect),
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect ∧
      0 ≤ tailRect.h ∧ 0 ≤ headRect.h ∧ y₀ < y₁ ∧
      pts = [⟨x, y₀⟩, ⟨x, y₁⟩] ∧
      tailRect.x ≤ x ∧ x ≤ tailRect.x + tailRect.w ∧
      headRect.x ≤ x ∧ x ≤ headRect.x + headRect.w ∧
      y₀ = tailRect.y + tailRect.h ∧ y₁ = headRect.y := by
  obtain ⟨q, ctx0, ox, oy, i, e, span, hmem, hctx, hoff, he, _, _, routing, hspan,
    hpts⟩ := hinst
  have hlt : span.top < span.bottom := straightSpanOf_top_lt hspan
  have hshape : pts = [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] := hpts
  have hcol := straightSpanOf_column_mem hspan
  obtain ⟨tailKey, headKey, tailRect, headRect, _, _, _, _, htr, hhr, hth, hhh,
    htx, htw, hhx, hhw, htop, hbot⟩ :=
    installed_span_rect_transport_tied execution hmem hctx hoff he hspan
  exact ⟨span.column, span.top, span.bottom, tailKey, headKey, tailRect, headRect,
    htr, hhr, hth, hhh, hlt, hshape, by rw [htx]; exact hcol.1,
    by rw [htx, htw]; exact hcol.2.1, by rw [hhx]; exact hcol.2.2.1,
    by rw [hhx, hhw]; exact hcol.2.2.2, htop, hbot⟩
/-- The scene route's points determine the straightened accumulator's points. -/
theorem SceneExecution.straight_points_of_scene {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {k : Nat} {id fromId toId : String} {orthogonal : Bool}
    {pts : List Point}
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
    execution.straight_canvasH
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

/-- The marked nodes split into the source prefix (same length as the input
nodes) and appended bottom nodes (all border `2`). Stated with opaque parts
so consumers never restate the prefix lambda. -/
private theorem installed_markNodes_split (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) :
    ∃ marked appended, Compound.markNodes boxes pad titles nodes = marked ++ appended ∧
      marked.length = nodes.length ∧
      (∀ r ∈ appended, r.border = 2) := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp only [List.length_map, List.length_zipIdx]
  · intro r hr
    obtain ⟨qq, hqq, heq⟩ := List.mem_filterMap.mp hr
    cases hrole : qq.1.role == .group with
    | true =>
      simp only [hrole, ↓reduceIte] at heq
      obtain rfl := Option.some.inj heq
      rfl
    | false =>
      simp [hrole] at heq

/-- A component key behind a real proper node names a source box: the graph
node at that key has border `0`, so the key lies below the marked prefix,
hence below the box count. -/
private theorem installed_key_lt_boxes {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {index : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp index)
      labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hd : nd.dummy = false) (hb : nd.node.border = 0)
    (hcomp : comp ∈ components execution.graph)
    {key : Nat} (hkey : comp[v]? = some key) :
    key < inp.boxes.length := by
  obtain ⟨n, hnCg, hnBorder⟩ := installed_proper_cg_node hrun hv hd hb
  have hcgmap : (componentCandidate execution.graph comp index).nodes =
      comp.map fun w => execution.graph.nodes.getD w default := by
    rw [componentCandidate_nodes]
    rfl
  rw [hcgmap, List.getElem?_map, hkey, Option.map_some] at hnCg
  have hfn : execution.graph.nodes.getD key default = n := Option.some.inj hnCg
  have hnB : (execution.graph.nodes.getD key default).border = 0 := by
    rw [hfn]
    exact hnBorder
  obtain ⟨r, hr⟩ := mem_components_eq hcomp
  have hkeyLt : key < execution.graph.nodes.length := by
    have h1 : key ∈ (List.range execution.graph.nodes.length).filter
        (fun w => (componentLab execution.graph)[w]! == r) := by
      rw [← hr]
      exact List.mem_of_getElem? hkey
    exact List.mem_range.mp (List.mem_filter.mp h1).1
  obtain ⟨N, hgraph, hNlen⟩ := installed_graph_marked execution
  have hlines := installed_lines_len execution
  have hN : N.length = inp.boxes.length := by
    rw [hNlen]
    exact hlines
  have hkeyTot : key < (Compound.markNodes
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box)
      execution.params.clusterPad
      (execution.lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * execution.params.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      N).length := by
    rw [← hgraph]
    exact hkeyLt
  obtain ⟨rr, hrGet⟩ : ∃ rr,
      (Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N)[key]? = some rr :=
    ⟨_, List.getElem?_eq_getElem hkeyTot⟩
  have hrn : rr = n := by
    have h1 : (Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N).getD key default = n := by
      have h2 : execution.graph.nodes.getD key default = n := hfn
      rwa [hgraph] at h2
    have h3 : ((Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N)[key]?).getD default = n := h1
    rwa [hrGet] at h3
  obtain ⟨marked, appended, hsplit, hmlen, hbord⟩ :=
    installed_markNodes_split _ _ _ N
  rw [hsplit] at hrGet
  rw [List.getElem?_append] at hrGet
  split at hrGet
  · simp only [hmlen] at *
    rw [← hN]
    assumption
  · have hmem := List.mem_of_getElem? hrGet
    have hb2 := hbord rr hmem
    rw [hrn] at hb2
    rw [hnBorder] at hb2
    exact absurd hb2 (by decide)

/-- A component candidate has as many nodes as the component list. -/
private theorem installed_comp_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  show (comp.map fun w => g.nodes.getD w default).length = comp.length
  simp

/-- A placed part has as many rectangles as the component graph has nodes. -/
private theorem installed_place_rects_length (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponent
  dsimp only
  simp only [List.length_map, List.length_range]

/-- The pack-step fold preserves the rectangles array size. -/
theorem installed_pack_fold_rects_size (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact (packStep_sizes _ _).1

/-- Packing preserves the rectangles array size. -/
theorem installed_packAcc_rects_size {P : Params} {o : Options} {mid out : Acc}
    (hpack : packAcc P o mid = .ok out) : out.rects.size = mid.rects.size := by
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  have he := Except.ok.inj hpack
  subst out
  change ((mid.parts.zip packed.boxes).foldl packStep
    { mid with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects.size = _
  rw [installed_pack_fold_rects_size]

/-- The component fold preserves the rectangles array size (copied from
`ExecutedPortsFacts.components_fold_rects_size`). -/
private theorem installed_fold_rects_size (P : Params) (inp : Input) (o : Options)
    (graph : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok out →
      out.rects.size = start.rects.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    rw [installed_fold_rects_size P inp o graph labels comps next out hrest]
    exact (layoutComponent_sizes hnext).1.symm

/-- The rectangles an installed route's endpoints name are the graph nodes of its
edge's tail and head positions in the part's component list. -/
theorem SceneExecution.installed_edge_keys {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat} {pts : List Point}
    (hinst : Installed execution.packedAcc key pts) :
    ∃ (i : Nat) (e : ProperEdge) (ctx0 : StraightenCtx) (q : List Nat × Part)
      (tailKey headKey : Nat) (tailRect headRect : Rect),
      ctx0.proper.edges[i]? = some e ∧ e.decl = key ∧ e.tail ≠ e.head ∧
      e.tail < q.1.length ∧ e.head < q.1.length ∧
      q.1[e.tail]? = some tailKey ∧ q.1[e.head]? = some headKey ∧
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect := by
  obtain ⟨q, ctx0, ox, oy, i, e, span, hmemP, hctx, hoff, he, hkey, hne, routing, hspan, _⟩ := hinst
  have hpartsEq := packAcc_parts_eq execution.packed_eq
  have hmemC : q ∈ execution.componentsAcc.parts := by
    rwa [hpartsEq] at hmemP
  obtain ⟨index, run, loops, area, hrun, hplace, hproper, hxs, hys, hdx, hdy⟩ :=
    installed_run_of_mem execution hmemC hctx
  obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_inv hspan
  have he'2 : ctx0.proper.edges[i]? = some e' := he'
  have heq : e' = e := Option.some.inj (he'2.symm.trans he)
  rw [heq] at he' helig
  have helig0 : straightEdgeEligible ctx0 routing i e = true := helig
  unfold straightEdgeEligible at helig0
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig0
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := helig0
  obtain ⟨tailNode, hvt, htd, htl, htb⟩ := straightRealNode_exists hTail
  obtain ⟨headNode, hvh, hhd, hhl, hhb⟩ := straightRealNode_exists hHead
  rw [hproper] at hvt hvh
  have htailLtCg : e.tail < (componentCandidate execution.graph q.1 index).nodes.length :=
    installed_proper_below hrun hvt htd htb
  have hheadLtCg : e.head < (componentCandidate execution.graph q.1 index).nodes.length :=
    installed_proper_below hrun hvh hhd hhb
  have hclen : (componentCandidate execution.graph q.1 index).nodes.length = q.1.length :=
    installed_comp_nodes_length _ _ _
  have htailLt : e.tail < q.1.length := by
    rw [← hclen]
    exact htailLtCg
  have hheadLt : e.head < q.1.length := by
    rw [← hclen]
    exact hheadLtCg
  obtain ⟨tailKey, htk⟩ : ∃ k, q.1[e.tail]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨htailLt, rfl⟩⟩
  obtain ⟨headKey, hhk⟩ : ∃ k, q.1[e.head]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨hheadLt, rfl⟩⟩
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hparts, _⟩ := actual_components_parts hempty execution.components_eq
  have hmember : (q.1, q.2) ∈ execution.componentsAcc.parts := hmemC
  have hcomp : q.1 ∈ components execution.graph := by
    have h1 : q.1 ∈ execution.componentsAcc.parts.map (·.1) :=
      List.mem_map_of_mem hmember
    rwa [hparts] at h1
  have hmidSize : execution.componentsAcc.rects.size = inp.boxes.length := by
    have hsz := installed_fold_rects_size execution.params inp o execution.graph execution.measured
      (components execution.graph) _ _ execution.components_eq
    rw [hsz]
    exact Array.size_replicate
  have hsizeT : tailKey < execution.packedAcc.rects.size := by
    have h1 : tailKey < inp.boxes.length :=
      installed_key_lt_boxes execution hrun hvt htd htb hcomp htk
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_packAcc_rects_size execution.packed_eq).symm
    omega
  have hsizeH : headKey < execution.packedAcc.rects.size := by
    have h1 : headKey < inp.boxes.length :=
      installed_key_lt_boxes execution hrun hvh hhd hhb hcomp hhk
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_packAcc_rects_size execution.packed_eq).symm
    omega
  have hsizeT_mid : tailKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact installed_key_lt_boxes execution hrun hvt htd htb hcomp htk
  have hsizeH_mid : headKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact installed_key_lt_boxes execution hrun hvh hhd hhb hcomp hhk
  have hpackEq := execution.packed_eq
  unfold packAcc at hpackEq
  obtain ⟨packed, hpacked, hprest⟩ := bind_ok hpackEq
  have hplen : execution.componentsAcc.parts.length = packed.boxes.length := by
    have hcount := Pack.pack_count hpacked
    rw [hcount, List.length_map]
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hmemC
  have hcLt : c < packed.boxes.length := by
    have h1 : c < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hc).1
    omega
  have hbox : packed.boxes[c]? = some packed.boxes[c] :=
    List.getElem?_eq_some_iff.mpr ⟨hcLt, rfl⟩
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (q, packed.boxes[c]) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hbox⟩
  have hrectsLen : q.2.rects.length = q.1.length := by
    have h1 := installed_place_rects_length execution.params
      (componentCandidate execution.graph q.1 index) run execution.measured loops
    have h2 := installed_comp_nodes_length execution.graph q.1 index
    rw [hplace, h1]
    exact h2
  have hRt : e.tail < q.2.rects.length := by
    rw [hrectsLen]
    exact htailLt
  have hRh : e.head < q.2.rects.length := by
    rw [hrectsLen]
    exact hheadLt
  obtain ⟨rectT, hrT⟩ : ∃ r, q.2.rects[e.tail]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRt⟩
  obtain ⟨rectH, hrH⟩ : ∃ r, q.2.rects[e.head]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRh⟩
  have hentryT : (q.1.zip q.2.rects)[e.tail]? = some (tailKey, rectT) :=
    List.getElem?_zip_eq_some.mpr ⟨htk, hrT⟩
  have hentryH : (q.1.zip q.2.rects)[e.head]? = some (headKey, rectH) :=
    List.getElem?_zip_eq_some.mpr ⟨hhk, hrH⟩
  have hvalT := installed_packed_rect_value hempty execution.components_eq execution.packed_eq
    packed hpacked hselected hentryT hsizeT_mid default
  have hvalH := installed_packed_rect_value hempty execution.components_eq execution.packed_eq
    packed hpacked hselected hentryH hsizeH_mid default
  have hlookT : execution.packedAcc.rects[tailKey]?
      = some (shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT) := by
    have hne : execution.packedAcc.rects[tailKey]? ≠ none := by
      intro hcon
      have hle := Array.getElem?_eq_none_iff.mp hcon
      omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hne
    have h2 : ((execution.packedAcc.rects[tailKey]?).getD default)
        = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalT
    have h3 : r = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  have hlookH : execution.packedAcc.rects[headKey]?
      = some (shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH) := by
    have hne : execution.packedAcc.rects[headKey]? ≠ none := by
      intro hcon
      have hle := Array.getElem?_eq_none_iff.mp hcon
      omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hne
    have h2 : ((execution.packedAcc.rects[headKey]?).getD default)
        = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalH
    have h3 : r = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  exact ⟨i, e, ctx0, q, tailKey, headKey, _, _, he, hkey, hne, htailLt, hheadLt, htk, hhk,
    hlookT, hlookH⟩

/-- `edgeOf` equation gives the declaration index, no reversal, and the model
boxes at the raw endpoints. Copy of `edgeOf_semantic_endpoints`. -/
private theorem srEdgeOfEndpoints
    {inp : Input} {route : ModelRoute} {index : Nat} {edge : Edge}
    (h : edgeOf inp route index = .ok edge) :
    edge.decl = index ∧ edge.reversed = false ∧
      ∃ source target : ModelBox,
        inp.boxes[edge.tail]? = some source ∧ source.id = route.fromId ∧
        inp.boxes[edge.head]? = some target ∧ target.id = route.toId := by
  unfold edgeOf at h
  cases hs : inp.boxes.findIdx? (fun box => box.id == route.fromId) with
  | none => simp only [hs] at h; contradiction
  | some sourceIndex =>
    cases ht : inp.boxes.findIdx? (fun box => box.id == route.toId) with
    | none => simp only [hs, ht] at h; contradiction
    | some targetIndex =>
      simp only [hs, ht, Except.ok.injEq] at h
      subst edge
      obtain ⟨hsbound, hsid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hs
      obtain ⟨htbound, htid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ht
      refine ⟨rfl, rfl, inp.boxes[sourceIndex], inp.boxes[targetIndex],
        List.getElem?_eq_getElem hsbound, ?_, List.getElem?_eq_getElem htbound, ?_⟩
      · exact beq_iff_eq.mp hsid
      · exact beq_iff_eq.mp htid

/-- Routes in a `graphEdgesFrom` output carry their own `edgeOf` equation.
Copy of `graphEdgesFrom_entry`. -/
private theorem srGraphEntry (inp : Input) :
    ∀ (routes : List ModelRoute) (offset : Nat) (edges : List Edge),
      graphEdgesFrom inp offset routes = .ok edges →
      ∀ (i : Nat) (edge : Edge), edges[i]? = some edge →
        ∃ route, routes[i]? = some route ∧ edgeOf inp route (offset + i) = .ok edge
  | [], _, edges, h, _, _, hi => by
    cases Except.ok.inj h
    simp at hi
  | route :: routes, offset, edges, h, i, edge, hi => by
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    cases Except.ok.inj h
    cases i with
    | zero =>
      have he : first = edge := Option.some.inj hi
      exact ⟨route, rfl, by simpa only [Nat.add_zero, he] using hfirst⟩
    | succ i =>
      obtain ⟨source, hs, he⟩ := srGraphEntry inp routes (offset + 1) rest hrest i edge hi
      refine ⟨source, hs, ?_⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using he

/-- Every measured-graph edge comes from an `edgeOf` raw edge through
`Compound.aliasEdge`. Copy of `measuredGraph_edge_source`. -/
private theorem srMeasuredSrc
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {edge : Edge} (hedge : edge ∈ graph.edges) :
    ∃ index route source,
      inp.routes[index]? = some route ∧ edgeOf inp route index = .ok source ∧
      edge = Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) source := by
  unfold measuredGraph at hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨edges, hedges, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  have hg := Except.ok.inj hgraph
  subst graph
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hedge
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hsource
  obtain ⟨route, hroute, hconstructor⟩ :=
    srGraphEntry inp inp.routes 0 edges hedges index source hindex
  exact ⟨index, route, source, hroute, by simpa only [Nat.zero_add] using hconstructor,
    heq.symm⟩

/-- `Edge.original` is idempotent. Copy of `original_idempotent`. -/
private theorem srOrigIdem (edge : Edge) : edge.original.original = edge.original := by
  cases hr : edge.reversed <;> simp [Edge.original, hr]

/-- `Edge.original` commutes with renumbering. Copy of `original_remap`. -/
private theorem srOrigRemap (edge : Edge) (f : Nat → Nat) :
    ({ edge with tail := f edge.tail, head := f edge.head }).original =
      { edge.original with tail := f edge.original.tail, head := f edge.original.head } := by
  cases hr : edge.reversed <;> simp [Edge.original, hr]

/-- `cycleGraph` preserves semantic edges. Copy of `cycleGraph_semantic_edges`. -/
private theorem srCycleSem (graph : Graph) :
    (cycleGraph graph).edges.map Edge.original = graph.edges.map Edge.original := by
  unfold cycleGraph
  split
  · exact ProtectedCycles.semantic_identity graph (Compound.constraints graph)
  · rw [breakCycles_edges_eq, List.map_map]
    apply List.map_congr_left
    intro edge _
    change (graph.orient edge).original = edge.original
    unfold Graph.orient
    split
    · exact Edge.reverse_original edge
    · rfl

/-- Candidate and component graphs agree on semantic edges. Copy of
`componentCandidate_semantic_edges`. -/
private theorem srCandSemEdges (graph : Graph) (component : List Nat)
    (index : Nat) :
    (componentCandidate graph component index).edges.map Edge.original =
      (componentGraph graph component).edges.map Edge.original := by
  unfold componentCandidate
  split
  · dsimp only
    split
    · rw [show ∀ g : Graph, (Compound.protect g).edges.map Edge.original =
          g.edges.map Edge.original from
          fun g => ProtectedCycles.semantic_identity g (Compound.constraints g),
        breakCyclesGreedy_semantic_identity]
      simp only [List.map_map, Function.comp_def, srOrigIdem]
    · rw [breakCyclesGreedy_semantic_identity]
      simp only [List.map_map, Function.comp_def, srOrigIdem]
  · rw [srCycleSem]
    simp only [List.map_map, Function.comp_def, srOrigIdem]

/-- Every candidate edge is the renumbered original of a graph edge whose tail
lies in the component. Copy of `componentCandidate_semantic_source`. -/
private theorem srCandSemSrc
    {graph : Graph} {component : List Nat} {index : Nat} {edge : Edge}
    (hedge : edge ∈ (componentCandidate graph component index).edges) :
    ∃ source ∈ graph.edges, source.tail ∈ component ∧
      edge.original = { source.original with
        tail := component.idxOf source.original.tail,
        head := component.idxOf source.original.head } := by
  have hm : edge.original ∈ (componentGraph graph component).edges.map Edge.original := by
    rw [← srCandSemEdges graph component index]
    exact List.mem_map_of_mem hedge
  obtain ⟨localEdge, hlocal, heq⟩ := List.mem_map.mp hm
  change localEdge ∈ (graph.edges.filter fun e => component.contains e.tail).map
    (fun e => { e with tail := component.idxOf e.tail, head := component.idxOf e.head }) at hlocal
  obtain ⟨source, hsource, hlocal⟩ := List.mem_map.mp hlocal
  obtain ⟨hsource, htail⟩ := List.mem_filter.mp hsource
  refine ⟨source, hsource, List.contains_iff_mem.mp htail, ?_⟩
  rw [← heq, ← hlocal]
  exact srOrigRemap source component.idxOf

/-- Candidate edges resolve to model routes and raw `edgeOf` edges. Copy of
`componentCandidate_model_endpoint_source`. -/
private theorem srModelSrc
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {component : List Nat} {candidate : Nat} {edge : Edge}
    (hedge : edge ∈ (componentCandidate graph component candidate).edges) :
    ∃ index route raw source target,
      inp.routes[index]? = some route ∧ edgeOf inp route index = .ok raw ∧
      edge.decl = index ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId ∧
      let prepared := inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box
      let aliased := Compound.aliasEdge prepared raw
      edge.original = { aliased with
        tail := component.idxOf aliased.tail, head := component.idxOf aliased.head } := by
  obtain ⟨globalEdge, hglobal, _, hsemantic⟩ := srCandSemSrc hedge
  obtain ⟨index, route, raw, hroute, hraw, halias⟩ := srMeasuredSrc hgraph hglobal
  obtain ⟨hdecl, hreversed, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    srEdgeOfEndpoints hraw
  have hglobalReversed : globalEdge.reversed = false := by
    rw [halias]
    exact hreversed
  have horiginal : globalEdge.original = globalEdge := by
    cases globalEdge with
    | mk tail head minLen decl reversed =>
      cases hglobalReversed
      rfl
  have hdecl' : edge.decl = index := by
    calc
      edge.decl = globalEdge.decl := by
        simpa only [Edge.original_decl] using congrArg Edge.decl hsemantic
      _ = raw.decl := by rw [halias]; rfl
      _ = index := hdecl
  refine ⟨index, route, raw, source, target, hroute, hraw, hdecl',
    hsource, hsourceId, htarget, htargetId, ?_⟩
  dsimp only
  rw [horiginal, halias] at hsemantic
  exact hsemantic

/-- Successful runs preserve the normalized edge set. Copy of
`componentRun_normalized_source`. -/
private theorem srNormSrc
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    ∃ ranks normalized,
      normalize cg ranks = .ok normalized ∧
      run.proper.edges = normalized.edges ∧
      run.proper.chains = normalized.chains := by
  obtain ⟨ranks, normalized, labeled, projected, hn, hlabels, hcoordinate,
    _, _, hproxy, hdrop, _⟩ := componentRun_spec hrun
  obtain ⟨hlabelEdges, _, hlabelChains, _⟩ := Labels.addLabelNodes_metadata hlabels
  have hclean : ∀ e ∈ (titleReservations (sizeProperPorts P labeled)).edges,
      e.synthetic = false := by
    intro e he
    have hedge : (titleReservations (sizeProperPorts P labeled)).edges =
        normalized.edges := hlabelEdges
    rw [hedge] at he
    exact normalize_clean hn e he
  have hprojectedEdges := (proxyWidths_rel hproxy).1
  have hdropEdges : (OrderImpl.dropSynthetic projected).edges =
      (OrderImpl.dropSynthetic
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
          P.clusterBorderW)).edges := by
    show projected.edges.filter (fun e => !e.synthetic) = _
    rw [hprojectedEdges, ← hcoordinate]
    rfl
  refine ⟨ranks, normalized, hn, ?_, ?_⟩
  · rw [← hdrop, hdropEdges,
      OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean]
    exact hlabelEdges
  · rw [← hdrop, OrderImpl.dropSynthetic_chains, proxyWidths_chains hproxy,
      ← hcoordinate, coordinateGraph_chains, hlabelChains]

/-- Every edge appended by `chainEdges` carries its own index. Copy of
`chainEdges_original`. -/
private theorem srChainOrig {e : Edge} {idx n0 s : Nat} {pe : ProperEdge}
    (hmem : pe ∈ NormalizeImpl.chainEdges e idx n0 s) : pe.original = idx := by
  unfold NormalizeImpl.chainEdges at hmem
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
  rfl

/-- A self-loop `normalizeEdge` keeps the edge list. Copy of
`normalizeEdge_self_edges`. -/
private theorem srNormSelfEdges {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (hself : e.tail = e.head)
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p') :
    p'.edges = p.edges := by
  unfold NormalizeImpl.normalizeEdge at h
  simp only [hself, ↓reduceIte, Except.ok.injEq] at h
  subst h
  rfl

/-- A non-self `normalizeEdge` appends only its own index. Copy of
`normalizeEdge_append_original`. -/
private theorem srNormAppendOrig {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (hne : e.tail ≠ e.head)
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p') {pe : ProperEdge}
    (hmem : pe ∈ p'.edges) (hnot : pe ∉ p.edges) : pe.original = idx := by
  unfold NormalizeImpl.normalizeEdge at h
  simp only [hne, ↓reduceIte] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · have heq := Except.ok.inj h
      subst p'
      have hmem2 : pe ∈ p.edges ++ NormalizeImpl.chainEdges e idx p.nodes.length _ :=
        hmem
      rcases List.mem_append.mp hmem2 with hm | hm
      · exact absurd hm hnot
      · exact srChainOrig hm

/-- No output edge carries a self-loop index. Copy of
`normalizeLoop_preserves_no_original`. -/
private theorem srNormLoopNo {es : List Edge} {slot : Int} {i : Nat}
    {l : List (Edge × Nat)} {p p' : Proper}
    (hmem : ∀ x ∈ l, es[x.2]? = some x.1)
    (hself : ∃ e, es[i]? = some e ∧ e.tail = e.head)
    (hno : ∀ pe ∈ p.edges, pe.original ≠ i)
    (h : NormalizeImpl.normalizeLoop slot l p = .ok p') :
    ∀ pe ∈ p'.edges, pe.original ≠ i := by
  induction l generalizing p with
  | nil =>
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hno
  | cons q rest ih =>
    obtain ⟨e, idx⟩ := q
    simp only [NormalizeImpl.normalizeLoop] at h
    split at h
    · simp at h
    · next p1 h1 =>
      have hmemHead : es[idx]? = some e := hmem (e, idx) (by simp)
      have hmemRest : ∀ x ∈ rest, es[x.2]? = some x.1 := fun x hx =>
        hmem x (List.mem_cons_of_mem _ hx)
      have hno1 : ∀ pe ∈ p1.edges, pe.original ≠ i := by
        intro pe hpe hcon
        by_cases hidx : idx = i
        · subst hidx
          have heq : e = hself.choose :=
            Option.some.inj (hmemHead.symm.trans hself.choose_spec.1)
          have hselfE : e.tail = e.head := by
            rw [heq]
            exact hself.choose_spec.2
          have hedge : p1.edges = p.edges :=
            srNormSelfEdges hselfE h1
          rw [hedge] at hpe
          exact hno pe hpe hcon
        · by_cases hselfE : e.tail = e.head
          · have hedge : p1.edges = p.edges :=
              srNormSelfEdges hselfE h1
            rw [hedge] at hpe
            exact hno pe hpe hcon
          · have horig := srNormAppendOrig hselfE h1 hpe
            by_cases hmemOld : pe ∈ p.edges
            · exact hno pe hmemOld hcon
            · have heq := horig hmemOld
              omega
      exact ih hmemRest hno1 h

/-- The zip-index list carries its own identity. Copy of `zipIdx_mem_identity`. -/
private theorem srZipIdx {es : List Edge} {x : Edge × Nat}
    (hx : x ∈ es.zipIdx) : es[x.2]? = some x.1 :=
  List.mem_zipIdx_iff_getElem?.mp hx

/-- A self-loop index contributes no normalized edge. Copy of
`normalized_no_original_of_self`. -/
private theorem srNormNoSelf {cg : Graph} {ranks : List Int} {p0 : Proper}
    (hn : normalize cg ranks = .ok p0)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∀ pe ∈ p0.edges, pe.original ≠ i := by
  have hmem : ∀ x ∈ cg.edges.zipIdx, cg.edges[x.2]? = some x.1 :=
    fun x hx => srZipIdx hx
  have hselfEx : ∃ e, cg.edges[i]? = some e ∧ e.tail = e.head :=
    ⟨edge, hedge, hself⟩
  have hno : ∀ (pe : ProperEdge), pe ∈
      (Proper.mk (cg.nodes.map (fun nd => ProperNode.mk nd false none false))
        [] ranks []).edges →
      pe.original ≠ i := by
    intro pe hpe
    simp at hpe
  unfold normalize at hn
  cases hslot : NormalizeImpl.slotOf cg with
  | none =>
    simp [hslot] at hn
  | some slot =>
    simp [hslot] at hn
    by_cases hcond : (cg.wellformed = true ∧ ranks.length = cg.nodes.length ∧ 0 ≤ slot)
    · simp [hcond] at hn
      have hn' : NormalizeImpl.normalizeLoop slot cg.edges.zipIdx
          (Proper.mk (cg.nodes.map (fun nd => ProperNode.mk nd false none false))
            [] ranks []) = .ok p0 := hn
      exact srNormLoopNo hmem hselfEx hno hn'
    · simp [hcond] at hn

/-- A self-loop edge contributes no proper chain segment. Copy of
`selfLoop_edgesOf_empty`. -/
private theorem srSelfEmpty {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {i : Nat} {edge : Edge}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hedge : cg.edges[i]? = some edge) (hself : edge.tail = edge.head) :
    (RouteImpl.edgesOf run.proper i) = [] := by
  obtain ⟨ranks, normalized, hn, he, _⟩ := srNormSrc hrun
  have hno : ∀ pe ∈ normalized.edges, pe.original ≠ i :=
    srNormNoSelf hn hedge hself
  have hno' : ∀ pe ∈ run.proper.edges, pe.original ≠ i := by
    rw [he]
    exact hno
  exact List.eq_nil_iff_forall_not_mem.mpr fun j hj =>
    absurd (mem_edgesOf.mp hj).2 (hno' _ (edgeAt_mem (mem_edgesOf.mp hj).1))

/-- A candidate edge whose model route is a self-loop is itself a self-loop:
`edgeOf` determinism gives a raw self-loop, `Compound.endpoint` preserves it,
and `Edge.original` with `idxOf` congruence carries it to the candidate. -/
private theorem srCandSelfOfRoute
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate : Nat} {edge : Edge}
    (hedge : edge ∈ (componentCandidate graph comp candidate).edges)
    {route : ModelRoute} (hroute : inp.routes[edge.decl]? = some route)
    (hself : route.fromId = route.toId) :
    edge.tail = edge.head := by
  obtain ⟨index, route', raw, source, target, hroute', hrawOf, hdeclIdx,
    hsource, hsourceId, htarget, htargetId, hsem⟩ :=
    srModelSrc hgraph hedge
  have hidx : index = edge.decl := hdeclIdx.symm
  have hrouteAt : inp.routes[index]? = some route := by
    rw [hidx]
    exact hroute
  have hrouteEq : route' = route := Option.some.inj (hroute'.symm.trans hrouteAt)
  rw [hrouteEq] at hrawOf
  have hrawSelf : raw.tail = raw.head := by
    unfold edgeOf at hrawOf
    have hpredEq : (fun b : ModelBox => b.id == route.fromId) =
        (fun b : ModelBox => b.id == route.toId) := by
      simp [hself]
    have hfindEq : inp.boxes.findIdx? (fun b => b.id == route.fromId) =
        inp.boxes.findIdx? (fun b => b.id == route.toId) := by
      rw [hpredEq]
    cases hfrom : inp.boxes.findIdx? (fun b => b.id == route.fromId) with
    | none =>
      have hto : inp.boxes.findIdx? (fun b => b.id == route.toId) = none := by
        rw [← hfindEq, hfrom]
      simp only [hfrom, hto] at hrawOf
      cases hrawOf
    | some a =>
      have hto : inp.boxes.findIdx? (fun b => b.id == route.toId) = some a := by
        rw [← hfindEq, hfrom]
      simp only [hfrom, hto, Except.ok.injEq] at hrawOf
      have htail : raw.tail = a := by
        rw [← hrawOf]
      have hhead : raw.head = a := by
        rw [← hrawOf]
      exact htail.trans hhead.symm
  have hendSelf : ∀ (boxes : List ModelBox) (s : Bool) (i j : Nat),
      i = j → Compound.endpoint boxes s i j = i := by
    intro boxes s i j hij
    subst hij
    unfold Compound.endpoint
    cases h : boxes[i]? with
    | none => rfl
    | some box => simp
  have haliasSelf : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) raw).tail =
      (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) raw).head := by
    unfold Compound.aliasEdge
    have e1 : Compound.endpoint (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) true raw.tail raw.head = raw.tail :=
      hendSelf _ _ _ _ hrawSelf
    have e2 : Compound.endpoint (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) false raw.head raw.tail = raw.head :=
      hendSelf _ _ _ _ hrawSelf.symm
    rw [e1, e2]
    exact hrawSelf
  dsimp only at hsem
  have htailEq : edge.original.tail =
      comp.idxOf (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) raw).tail := congrArg Edge.tail hsem
  have hheadEq : edge.original.head =
      comp.idxOf (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) raw).head := congrArg Edge.head hsem
  have horigSelf : edge.original.tail = edge.original.head := by
    rw [htailEq, hheadEq, haliasSelf]
  cases hr : edge.reversed with
  | true =>
    simp only [Edge.original, hr] at horigSelf ⊢
    exact horigSelf.symm
  | false =>
    simp only [Edge.original, hr] at horigSelf ⊢
    exact horigSelf

/-- The model keys of the route a corridor replaces: the input route's from and to ids
are the tail and head model boxes of the edge, up to reversal. -/
theorem SceneExecution.installed_route_ends {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat} {pts : List Point}
    (hinst : Installed execution.packedAcc key pts) {route : ModelRoute}
    (hroute : inp.routes[key]? = some route) :
    route.fromId ≠ route.toId := by
  intro hcon
  obtain ⟨q, ctx0, ox, oy, i, e, span, hmem, hctx, hoff, he0, hkey, hne, hspan⟩ := hinst
  have hqmem : q ∈ execution.componentsAcc.parts := by
    have hp := packAcc_parts_eq execution.packed_eq
    rw [hp] at hmem
    exact hmem
  obtain ⟨index, run, loops, area, hrun, hloops, hplace, _, _, _⟩ :=
    execution.actual_component_sizing hqmem
  have hstraight : (placeComponent execution.params
      (componentCandidate execution.graph q.1 index) run 0 execution.measured
      loops).straighten = some ctx0 := by
    have hctxcopy := hctx
    rw [hplace] at hctxcopy
    exact hctxcopy
  unfold placeComponent at hstraight
  dsimp only at hstraight
  obtain rfl := Option.some.inj hstraight
  have hmemE : e ∈ run.proper.edges := List.mem_of_getElem? he0
  obtain ⟨ge, hge, hdeclge⟩ := componentRun_declInv hrun e hmemE
  have hgeDecl : ge.decl = key := hdeclge.symm.trans hkey
  have hgeMem : ge ∈ (componentCandidate execution.graph q.1 index).edges :=
    List.mem_of_getElem? hge
  have hrouteGe : inp.routes[ge.decl]? = some route := by
    rw [hgeDecl]
    exact hroute
  have hgeSelf : ge.tail = ge.head :=
    srCandSelfOfRoute execution.graph_eq hgeMem hrouteGe hcon
  have hempty : (RouteImpl.edgesOf run.proper e.original) = [] :=
    srSelfEmpty hrun hge hgeSelf
  have hiLt : i < run.proper.edges.length := (List.getElem?_eq_some_iff.mp he0).1
  have hedgeAt : RouteImpl.edgeAt run.proper i = e := by
    unfold RouteImpl.edgeAt
    rw [List.getD_eq_getElem?_getD, he0, Option.getD_some]
  have hmemEdges : i ∈ RouteImpl.edgesOf run.proper e.original :=
    mem_edgesOf.mpr ⟨hiLt, by rw [hedgeAt]⟩
  rw [hempty] at hmemEdges
  simp at hmemEdges

set_option maxHeartbeats 800000
/-- Component lookup at the position of a member. Copy of `comp_idxOf_lookup`. -/
private theorem slIdxLookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- On a duplicate-free component, `idxOf` is injective. Copy of
`comp_idxOf_injective`. -/
private theorem slIdxInj {comp : List Nat}
    {x y : Nat} (hx : x ∈ comp) (hy : y ∈ comp)
    (h : comp.idxOf x = comp.idxOf y) : x = y := by
  have e0 : comp[comp.idxOf x]? = comp[comp.idxOf y]? := by rw [h]
  have eL : comp[comp.idxOf x]? = some x := slIdxLookup hx
  have eR : comp[comp.idxOf y]? = some y := slIdxLookup hy
  exact Option.some.inj (eL.symm.trans (e0.trans eR))

/-- `idxOf` below length names a member. Via `idxOf_lt_length_iff`. -/
private theorem slIdxMemOfLt {l : List Nat} {x : Nat}
    (h : l.idxOf x < l.length) : x ∈ l :=
  List.idxOf_lt_length_iff.mp h

/-- Endpoint case split on prepared boxes. Copy of `endpoint_cases_local`. -/
private theorem slEndpointCases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
    Compound.endpoint boxes s i j = i ∨
      (Compound.endpoint boxes s i j = Compound.bottomIndex boxes i ∧
        ∀ box, boxes[i]? = some box → box.role = .group) := by
  unfold Compound.endpoint
  cases hbi : boxes[i]? with
  | none => exact Or.inl rfl
  | some box =>
    cases hbj : boxes[j]? with
    | none => exact Or.inl rfl
    | some target =>
      dsimp only
      by_cases hc : (box.role != .group || i == j) = true
      · rw [ite_eq_left hc]
        exact Or.inl rfl
      · rw [ite_eq_right hc]
        by_cases hd : (s == Compound.inside boxes box.id target.id) = true
        · rw [ite_eq_left hd]
          exact Or.inl rfl
        · rw [ite_eq_right hd]
          refine Or.inr ⟨rfl, ?_⟩
          intro box' hb'
          have heq : box' = box := (Option.some.inj hb').symm
          rw [heq]
          cases hbr : box.role
          · exfalso
            have h1 : (box.role != .group || i == j) = true := by
              rw [hbr]
              cases hij : (i == j) <;> rfl
            exact hc h1
          · rfl

/-- `bottomIndex` is strictly increasing past a group box. Copy of
`flat_bottomIndex_lt`. -/
private theorem slBottomLt {boxes : List ModelBox} {i j : Nat}
    (hij : i < j) (hi : i < boxes.length)
    (hg : (boxes[i]'hi).role == .group) :
    Compound.bottomIndex boxes i < Compound.bottomIndex boxes j := by
  have h1 : (boxes.take j).take i ++ (boxes.take j).drop i = boxes.take j :=
    List.take_append_drop i (boxes.take j)
  have h2 : (boxes.take j).take i = boxes.take i := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have h3 := congrArg (List.filter (fun box : ModelBox => box.role == .group)) h1
  rw [List.filter_append, h2] at h3
  have hmem : boxes[i]'hi ∈ (boxes.take j).drop i := by
    have h0 : ((boxes.take j).drop i)[0]? = some (boxes[i]'hi) := by
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_take, ite_eq_left hij,
        List.getElem?_eq_getElem hi]
    exact List.mem_of_getElem? h0
  have hfilter : 0 < (((boxes.take j).drop i).filter
      (fun box : ModelBox => box.role == .group)).length := by
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hmem, hg⟩
  have h4 := congrArg (fun l => l.length) h3
  rw [List.length_append] at h4
  unfold Compound.bottomIndex
  omega

/-- Two group-box indices with the same `bottomIndex` coincide. Copy of
`flat_bottomIndex_injective`. -/
private theorem slBottomInj {boxes : List ModelBox} {i j : Nat}
    {bi bj : ModelBox} (hbi : boxes[i]? = some bi) (hbj : boxes[j]? = some bj)
    (hgi : bi.role == .group) (hgj : bj.role == .group)
    (h : Compound.bottomIndex boxes i = Compound.bottomIndex boxes j) : i = j := by
  obtain ⟨hi, hie⟩ := List.getElem_of_getElem? hbi
  obtain ⟨hj, hje⟩ := List.getElem_of_getElem? hbj
  rw [← hie] at hgi
  rw [← hje] at hgj
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (slBottomLt hlt hi hgi))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (slBottomLt hgt hj hgj))

/-- Prepared boxes for aliasing: fixed-size boxes act as nodes. Short name keeps
explicit-list terms small in the self-loop proof. -/
private def slPrepared (inp : Input) : List ModelBox :=
  inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
    else box

/-- Lookup through the prepared list. Copy of `preparedBoxes_lookup`. -/
private theorem slPreparedLookup {inp : Input} {j : Nat} {src : ModelBox}
    (hsrc : inp.boxes[j]? = some src) :
    (slPrepared inp)[j]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src) := by
  unfold slPrepared
  rw [List.getElem?_map, hsrc]
  simp


/-- Candidate nodes are the component-mapped graph nodes. Copy of
`componentCandidate_nodes`. -/
private theorem slCandNodes (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes = (componentGraph g comp).nodes := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

/-- The input route of a component's self-loop edge is a self-loop: a candidate edge
whose tail and head coincide declares a route with equal from and to ids. -/
theorem SceneExecution.self_edge_route_ends {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {q : List Nat × Part} {candidate : Nat}
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1 candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) {run : Run}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1 candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    {route : ModelRoute}
    (hroute : inp.routes[edge.decl]? = some route) :
    route.fromId = route.toId := by
  have hmem : edge ∈ (componentCandidate execution.graph q.1 candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨index, route', raw, source, target, hroute', hrawOf, hdeclIdx,
    hsource, hsourceId, htarget, htargetId, hsem⟩ :=
    srModelSrc execution.graph_eq hmem
  have hidx : index = edge.decl := hdeclIdx.symm
  have hrouteAt : inp.routes[index]? = some route := by
    rw [hidx]
    exact hroute
  have hrouteEq : route' = route := Option.some.inj (hroute'.symm.trans hrouteAt)
  rw [hrouteEq] at hrawOf hsourceId htargetId
  have hprepared : (slPrepared inp).length = inp.boxes.length := by
    unfold slPrepared
    simp
  dsimp only at hsem
  have hsemS : edge.original = {Compound.aliasEdge (slPrepared inp) raw with
      tail := q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail,
      head := q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).head} := hsem
  have horigSelf : edge.original.tail = edge.original.head := by
    cases hr : edge.reversed with
    | true => simp [Edge.original, hr, hself]
    | false => simp [Edge.original, hr, hself]
  have htailEq : edge.original.tail =
      q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail :=
    congrArg Edge.tail hsemS
  have hheadEq : edge.original.head =
      q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).head :=
    congrArg Edge.head hsemS
  have hidxEq : q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail =
      q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).head := by
    rw [← htailEq, ← hheadEq, horigSelf]
  have hbounds : edge.tail < (componentCandidate execution.graph q.1 candidate).nodes.length ∧
      edge.head < (componentCandidate execution.graph q.1 candidate).nodes.length := by
    obtain ⟨ranks, normalized, hn, _, _⟩ := srNormSrc hrun
    have hwf := (normalize_node_rank_alignment hn).2
    have hb := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
    exact ⟨hb.1, hb.2.1⟩
  have hlen : (componentCandidate execution.graph q.1 candidate).nodes.length = q.1.length := by
    rw [slCandNodes]
    unfold componentGraph
    simp only [List.length_map]
  have hboundsQ : edge.tail < q.1.length ∧ edge.head < q.1.length := by
    rw [hlen] at hbounds
    exact hbounds
  have hedgeTailLt : q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail < q.1.length := by
    rw [← htailEq]
    cases hr : edge.reversed with
    | true =>
      simp only [Edge.original, hr]
      exact hboundsQ.2
    | false =>
      simp only [Edge.original, hr]
      exact hboundsQ.1
  have hedgeHeadLt : q.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).head < q.1.length := by
    rw [← hheadEq]
    cases hr : edge.reversed with
    | true =>
      simp only [Edge.original, hr]
      exact hboundsQ.1
    | false =>
      simp only [Edge.original, hr]
      exact hboundsQ.2
  have htailMem : (Compound.aliasEdge (slPrepared inp) raw).tail ∈ q.1 :=
    slIdxMemOfLt hedgeTailLt
  have hheadMem : (Compound.aliasEdge (slPrepared inp) raw).head ∈ q.1 :=
    slIdxMemOfLt hedgeHeadLt
  have haliased : (Compound.aliasEdge (slPrepared inp) raw).tail =
      (Compound.aliasEdge (slPrepared inp) raw).head :=
    slIdxInj htailMem hheadMem hidxEq
  have hT : (Compound.aliasEdge (slPrepared inp) raw).tail =
      Compound.endpoint (slPrepared inp) true raw.tail raw.head := rfl
  have hH : (Compound.aliasEdge (slPrepared inp) raw).head =
      Compound.endpoint (slPrepared inp) false raw.head raw.tail := rfl
  rcases slEndpointCases (boxes := slPrepared inp) true raw.tail raw.head with hflatT | ⟨hbotT, hgrpT⟩
  · rcases slEndpointCases (boxes := slPrepared inp) false raw.head raw.tail with hflatH | ⟨hbotH, hgrpH⟩
    · rw [hT, hflatT, hH, hflatH] at haliased
      have hst : source = target := by
        rw [haliased] at hsource
        exact Option.some.inj (hsource.symm.trans htarget)
      exact hsourceId.symm.trans (by rw [hst]; exact htargetId)
    · rw [hT, hflatT, hH, hbotH] at haliased
      have hlt : raw.tail < (slPrepared inp).length := by
        simpa [hprepared] using (List.getElem?_eq_some_iff.mp hsource).1
      have hge : (slPrepared inp).length ≤
          Compound.bottomIndex (slPrepared inp) raw.head := by
        unfold Compound.bottomIndex
        omega
      omega
  · rcases slEndpointCases (boxes := slPrepared inp) false raw.head raw.tail with hflatH | ⟨hbotH, hgrpH⟩
    · rw [hT, hbotT, hH, hflatH] at haliased
      have hlt : raw.head < (slPrepared inp).length := by
        simpa [hprepared] using (List.getElem?_eq_some_iff.mp htarget).1
      have hge : (slPrepared inp).length ≤
          Compound.bottomIndex (slPrepared inp) raw.tail := by
        unfold Compound.bottomIndex
        omega
      omega
    · rw [hT, hbotT, hH, hbotH] at haliased
      have hsame : raw.tail = raw.head :=
        slBottomInj (slPreparedLookup hsource)
          (slPreparedLookup htarget)
          (by simp [hgrpT _ (slPreparedLookup hsource)])
          (by simp [hgrpH _ (slPreparedLookup htarget)]) haliased
      have hst : source = target := by
        rw [hsame] at hsource
        exact Option.some.inj (hsource.symm.trans htarget)
      exact hsourceId.symm.trans (by rw [hst]; exact htargetId)

/-- The installer is the part that owns the edge: any installed-route witness and any
selected component edge with the same declaration name the same component, the same
part, and the same candidate edge index. Span geometry and offsets are not consulted. -/
theorem SceneExecution.installed_edge_installer (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (_hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1.1 candidate) execution.measured (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops with area := area }) :
    ∀ (qS : List Nat × Part) (ctx0 : StraightenCtx) (j : Nat) (eS : ProperEdge),
      qS ∈ execution.packedAcc.parts →
      qS.2.straighten = some ctx0 →
      ctx0.proper.edges[j]? = some eS →
      eS.decl = key →
      qS.1 = q.1.1 ∧ qS.2 = q.1.2 ∧ eS.original = i := by
  intro qS ctx0 j eS hmemS hctxS heS hdeclS
  have hpackEq : execution.packedAcc.parts = execution.componentsAcc.parts :=
    packAcc_parts_eq execution.packed_eq
  have hmemSq : qS ∈ execution.componentsAcc.parts := by
    rw [← hpackEq]
    exact hmemS
  have hmemQ : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  obtain ⟨hpartsEq, _⟩ := actual_components_parts (by rfl) execution.components_eq
  have hcompS : qS.1 ∈ components execution.graph := by
    rw [← hpartsEq]
    exact List.mem_map_of_mem hmemSq
  have hcompQ : q.1.1 ∈ components execution.graph := by
    rw [← hpartsEq]
    exact List.mem_map_of_mem hmemQ
  obtain ⟨indexS, runS, loopsS, areaS, hrunS, hplaceS, hproperS, _, _, _, _⟩ :=
    installed_run_of_mem execution hmemSq hctxS
  have heSrun : eS ∈ runS.proper.edges := by
    rw [← hproperS]
    exact List.mem_of_getElem? heS
  obtain ⟨geS, hgeS, hdeclgeS⟩ := componentRun_declInv hrunS eS heSrun
  have hownsS : ownsDecl execution.graph qS.1 key := by
    have h0 := componentCandidate_edge_owns (List.mem_of_getElem? hgeS)
    have h1 : geS.decl = key := hdeclgeS.symm.trans hdeclS
    rw [h1] at h0
    exact h0
  have hownsQ : ownsDecl execution.graph q.1.1 key := by
    have h0 := componentCandidate_edge_owns (List.mem_of_getElem? hedge)
    rw [hdecl] at h0
    exact h0
  have hcompEq : qS.1 = q.1.1 :=
    ownsDecl_unique (measuredGraph_decls_nodup execution.graph_eq) hcompS hcompQ hownsS hownsQ
  have hpartsNodup : (execution.componentsAcc.parts.map (·.1)).Nodup := by
    rw [hpartsEq]
    exact components_entries_nodup _
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hmemSq
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hmemQ
  have ha' : a < (execution.componentsAcc.parts.map (·.1)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp ha).1
  have hb' : b < (execution.componentsAcc.parts.map (·.1)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hb).1
  have hma : (execution.componentsAcc.parts.map (·.1))[a]? = some qS.1 := by
    rw [List.getElem?_map, ha]
    simp
  have hmb : (execution.componentsAcc.parts.map (·.1))[b]? = some q.1.1 := by
    rw [List.getElem?_map, hb]
    simp
  have hab : a = b :=
    hpartsNodup.eq_of_getElem?_eq ha' (by rw [hma, hmb, hcompEq])
  have hpair : qS = q.1 := by
    rw [hab] at ha
    exact Option.some.inj (ha.symm.trans hb)
  have hq2 : qS.2 = q.1.2 := congrArg Prod.snd hpair
  have hstraightC : (placeComponent execution.params (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops).straighten = some ctx0 := by
    have hc := hctxS
    rw [hq2, hpart] at hc
    exact hc
  unfold placeComponent at hstraightC
  dsimp only at hstraightC
  obtain rfl := Option.some.inj hstraightC
  have heS' : run.proper.edges[j]? = some eS := heS
  have hmemE : eS ∈ run.proper.edges := List.mem_of_getElem? heS'
  obtain ⟨geS', hgeS', hdeclgeS'⟩ := componentRun_declInv hrun eS hmemE
  have hdeclEq : geS'.decl = edge.decl := hdeclgeS'.symm.trans (hdeclS.trans hdecl.symm)
  have hnd : ((componentCandidate execution.graph q.1.1 candidate).edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq _ _
  have hidx : eS.original = i := nodup_map_inj (·.decl) hnd hgeS' hedge hdeclEq
  exact ⟨hcompEq, hq2, hidx⟩

/-- The candidate edge a straightened corridor installs is not reversed: straightening
only accepts edges whose context `reversed` entry is `false`, and that entry is the
candidate graph's own flag at the edge's original index. -/
theorem SceneExecution.installed_edge_not_reversed (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area }) :
    edge.reversed = false := by
  obtain ⟨qS, ctx0, ox, oy, j, e, span, hmem, hctx, hoff, he0, hkey, hne, routing, hspan,
    hpts⟩ := hinst
  obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_inv hspan
  have hid := execution.installed_edge_installer (q := q) (packed := packed) (c := c)
    ⟨qS, ctx0, ox, oy, j, e, span, hmem, hctx, hoff, he0, hkey, hne, routing, hspan, hpts⟩
    hselected hedge hdecl hrun hpart qS ctx0 j e hmem hctx he0 hkey
  have heqE : e' = e := Option.some.inj (he'.symm.trans he0)
  rw [heqE] at helig
  have hrev : (ctx0.reversed.getD i false) = false := by
    have h := helig
    unfold straightEdgeEligible at h
    simp_all only [Bool.and_eq_true, Bool.not_eq_true']
  have hstraight : (placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0 := by
    have hc := hctx
    rw [hid.2.1, hpart] at hc
    exact hc
  unfold placeComponent at hstraight
  dsimp only at hstraight
  obtain rfl := Option.some.inj hstraight
  have hrev' : ((componentCandidate execution.graph q.1.1 candidate).edges.map
      (·.reversed)).getD i false = false := hrev
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some,
    Option.getD_some] at hrev'
  exact hrev'
/-- A placed part's straightening context carries the run's proper graph. -/
private theorem placeComponent_straighten_proper (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    ((placeComponent P cg run cursor labels loops).straighten.map (·.proper)) =
      some run.proper := rfl
/-- A single `normalizeEdge` does not shrink the node list. -/
private theorem normEdge_grow {slot : Int} {p q : Proper} {e : Edge} {idx : Nat}
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok q) :
    p.nodes.length ≤ q.nodes.length := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · have heq := Except.ok.inj h
    subst q
    exact Nat.le_refl _
  · split at h
    · simp at h
    · split at h
      · simp at h
      · have heq := Except.ok.inj h
        subst q
        simp [NormalizeImpl.appendChain]

/-- Every proper edge of a successful `normalizeLoop` is old or an appended chain
segment: each step appends only its own index's `chainEdges`, and node lists
only grow, so the segment base `n0` covers the loop-entry length. -/
private theorem normLoop_mem_chain {slot : Int} :
    ∀ (l : List (Edge × Nat)) (q q' : Proper),
      NormalizeImpl.normalizeLoop slot l q = .ok q' →
      ∀ pe ∈ q'.edges,
      pe ∈ q.edges ∨
        ∃ e idx n0 s, (e, idx) ∈ l ∧ pe ∈ NormalizeImpl.chainEdges e idx n0 s ∧
          q.nodes.length ≤ n0 := by
  intro l
  induction l with
  | nil =>
    intro q q' h pe hmem
    have he : q = q' := Except.ok.inj h
    subst q'
    exact Or.inl hmem
  | cons hd tl ih =>
    intro q q' h pe hmem
    obtain ⟨e, idx⟩ := hd
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      have hgrow : q.nodes.length ≤ q1.nodes.length := by
        unfold NormalizeImpl.normalizeEdge at h1
        split at h1
        · have heq := Except.ok.inj h1
          subst q1
          exact Nat.le_refl _
        · split at h1
          · simp at h1
          · split at h1
            · simp at h1
            · have heq := Except.ok.inj h1
              subst q1
              simp [NormalizeImpl.appendChain]
      have hrest := ih q1 q' h pe hmem
      rcases hrest with hq1 | ⟨e', idx', n0, s, hmemL, hchain, hle⟩
      · unfold NormalizeImpl.normalizeEdge at h1
        split at h1
        · have heq := Except.ok.inj h1
          subst q1
          exact Or.inl hq1
        · split at h1
          · simp at h1
          · split at h1
            · simp at h1
            · have heq := Except.ok.inj h1
              subst q1
              simp only [NormalizeImpl.appendChain] at hq1
              rcases List.mem_append.mp hq1 with hL | hR
              · exact Or.inl hL
              · exact Or.inr ⟨e, idx, _, _, List.mem_cons.mpr (Or.inl rfl), hR,
                  Nat.le_refl _⟩
      · exact Or.inr ⟨e', idx', n0, s, List.mem_cons_of_mem _ hmemL, hchain,
          Nat.le_trans hgrow hle⟩

/-- An installed edge is the whole chain: a proper edge with the installed
`original` whose ends index component nodes is the chain's single segment,
since intermediate chain nodes sit at or above the component length. -/
theorem SceneExecution.installed_edge_positions (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (_hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (_hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1.1 candidate) execution.measured (candidateOrder candidate) = .ok run)
    (_hpart : q.1.2 = { placeComponent execution.params (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops with area := area }) :
    ∀ (eS : ProperEdge), eS ∈ run.proper.edges → eS.original = i →
      (∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.tail]? = some n) →
      (∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.head]? = some n) →
      eS.tail = edge.tail ∧ eS.head = edge.head := by
  intro eS hmemS hOrig hTailEx hHeadEx
  obtain ⟨_, hTailCg⟩ := hTailEx
  obtain ⟨_, hHeadCg⟩ := hHeadEx
  obtain ⟨ranks, normalized, hn, he, _⟩ := srNormSrc hrun
  have hmemN : eS ∈ normalized.edges := by
    rw [← he]
    exact hmemS
  have hcgLen : (componentCandidate execution.graph q.1.1 candidate).nodes.length =
      q.1.1.length :=
    installed_comp_nodes_length _ _ _
  have hTailLt : eS.tail < q.1.1.length := by
    rw [← hcgLen]
    exact (List.getElem?_eq_some_iff.mp hTailCg).1
  have hHeadLt : eS.head < q.1.1.length := by
    rw [← hcgLen]
    exact (List.getElem?_eq_some_iff.mp hHeadCg).1
  unfold NormalizeImpl.normalize at hn
  split at hn
  · simp at hn
  · next slot hs =>
    split at hn
    · have hmemOr := normLoop_mem_chain _ _ _ hn eS hmemN
      rcases hmemOr with h0 | ⟨e', idx, n0, s, hmemL, hchain, hle0⟩
      · simp at h0
      · have hOrigIdx : idx = i := (srChainOrig hchain).symm.trans hOrig
        rw [hOrigIdx] at hchain hmemL
        have hge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? =
            some e' :=
          srZipIdx hmemL
        have heq : e' = edge := Option.some.inj (hge.symm.trans hedge)
        rw [heq] at hchain
        have hle0' : q.1.1.length ≤ n0 := by
          simpa [hcgLen] using hle0
        simp only [NormalizeImpl.chainEdges, List.mem_map, List.mem_range] at hchain
        obtain ⟨k, hkS, rfl⟩ := hchain
        have hTailLt' : NormalizeImpl.chainNode edge.tail edge.head n0 s k <
            q.1.1.length :=
          hTailLt
        have hHeadLt' : NormalizeImpl.chainNode edge.tail edge.head n0 s (k + 1) <
            q.1.1.length :=
          hHeadLt
        have hk0 : k = 0 := by
          refine Classical.byContradiction fun hk0 => ?_
          by_cases hks : k = s
          · omega
          · simp only [NormalizeImpl.chainNode, hk0, hks, ↓reduceIte] at hTailLt'
            omega
        subst hk0
        have hk1 : 0 + 1 = s := by
          refine Classical.byContradiction fun hk1 => ?_
          have hk10 : (0 : Nat) + 1 ≠ 0 := by omega
          simp only [NormalizeImpl.chainNode, hk10, hk1, ↓reduceIte] at hHeadLt'
          omega
        have hs1 : s = 1 := by omega
        subst hs1
        show edge.tail = edge.tail ∧ edge.head = edge.head
        exact ⟨rfl, rfl⟩
    · simp at hn
/-- The proper edge of an installed route has the component edge's endpoints. -/
theorem SceneExecution.installed_edge_endpoints (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (_hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1.1 candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area }) :
    ∀ (qS : List Nat × Part) (ctx0 : StraightenCtx) (j : Nat) (eS : ProperEdge),
      qS ∈ execution.packedAcc.parts →
      qS.2.straighten = some ctx0 →
      ctx0.proper.edges[j]? = some eS →
      eS.decl = key →
      ∀ {routing : Routing} {span : StraightSpan} {ox oy : Int},
      straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing j =
        .ok (some span) →
      eS.tail = edge.tail ∧ eS.head = edge.head := by
  intro qS ctx0 j eS hmem hctx he hdeclS _routing _span _ox _oy hspan
  have hid := execution.installed_edge_installer _hinst hselected hedge hdecl hrun hpart
    qS ctx0 j eS hmem hctx he hdeclS
  obtain ⟨_hq1, hq2, hOrig⟩ := hid
  have hstraightC : (placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0 := by
    have hc := hctx
    rw [hq2, hpart] at hc
    exact hc
  unfold placeComponent at hstraightC
  dsimp only at hstraightC
  obtain rfl := Option.some.inj hstraightC
  have hmemE : eS ∈ run.proper.edges := List.mem_of_getElem? he
  obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_inv hspan
  have heq : e' = eS := Option.some.inj (he'.symm.trans he)
  rw [heq] at helig
  have helig0 : straightEdgeEligible _ _ j eS = true := helig
  unfold straightEdgeEligible at helig0
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig0
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := helig0
  obtain ⟨tailNode, hvt0, htd, htl, htb⟩ := straightRealNode_exists hTail
  obtain ⟨headNode, hvh0, hhd, hhl, hhb⟩ := straightRealNode_exists hHead
  have hvt : run.proper.nodes[eS.tail]? = some tailNode := hvt0
  have hvh : run.proper.nodes[eS.head]? = some headNode := hvh0
  have htailLtCg : eS.tail < (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    installed_proper_below hrun hvt htd htb
  have hheadLtCg : eS.head < (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    installed_proper_below hrun hvh hhd hhb
  have hTailEx : ∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.tail]? =
      some n :=
    ⟨_, List.getElem?_eq_getElem htailLtCg⟩
  have hHeadEx : ∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.head]? =
      some n :=
    ⟨_, List.getElem?_eq_getElem hheadLtCg⟩
  exact execution.installed_edge_positions _hinst hselected hedge hdecl hrun hpart eS
    hmemE hOrig hTailEx hHeadEx

/-- A component key below the prepared-box count cannot name a `bottomIndex`:
aliased endpoints below the box count are flat. -/
private theorem endpoint_flat_of_bound {P : List ModelBox} {s : Bool} {i j key : Nat}
    (heq : key = Compound.endpoint P s i j) (hlt : key < P.length) : key = i := by
  rcases slEndpointCases (boxes := P) s i j with hflat | ⟨hbot, _⟩
  · rw [heq]
    exact hflat
  · have hbig : P.length ≤ key := by
      rw [heq, hbot]
      unfold Compound.bottomIndex
      exact Nat.le_add_right _ _
    exact False.elim (absurd hbig (Nat.not_le_of_gt hlt))

/-- The model keys of a candidate edge name its input route's source and target
boxes: the declaration resolves to a raw edge and model boxes, and both ends
index below the component length, so the aliased endpoints are component keys. -/
private theorem installed_route_model_keys
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate : Nat} {edge : Edge}
    (hmem : edge ∈ (componentCandidate graph comp candidate).edges)
    {key : Nat} (hdecl : edge.decl = key)
    {route : ModelRoute} (hroute : inp.routes[key]? = some route)
    (hrev : edge.reversed = false)
    (htailLt : edge.tail < comp.length) (hheadLt : edge.head < comp.length) :
    ∃ (raw : Edge) (source target : ModelBox),
      edgeOf inp route key = .ok raw ∧
      comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail = edge.tail ∧
      comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).head = edge.head ∧
      comp[comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail]? =
        some (Compound.aliasEdge (slPrepared inp) raw).tail ∧
      comp[comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).head]? =
        some (Compound.aliasEdge (slPrepared inp) raw).head ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId := by
  obtain ⟨index, route', raw, source, target, hroute', hrawOf, hdeclIdx, hsource,
    hsourceId, htarget, htargetId, hsem⟩ :=
    srModelSrc hgraph hmem
  have hidxKey : index = key := hdeclIdx.symm.trans hdecl
  have hrouteAt : inp.routes[index]? = some route := by
    rw [hidxKey]
    exact hroute
  have hrouteEq : route' = route := Option.some.inj (hroute'.symm.trans hrouteAt)
  have hrawOf' : edgeOf inp route key = .ok raw := by
    rw [← hidxKey, ← hrouteEq]
    exact hrawOf
  dsimp only at hsem
  have htailEq : edge.original.tail =
      comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail :=
    congrArg Edge.tail hsem
  have hheadEq : edge.original.head =
      comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).head :=
    congrArg Edge.head hsem
  have htailOrig : edge.original.tail = edge.tail := by simp [Edge.original, hrev]
  have hheadOrig : edge.original.head = edge.head := by simp [Edge.original, hrev]
  have hcompTail : comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail =
      edge.tail :=
    htailEq.symm.trans htailOrig
  have hcompHead : comp.idxOf (Compound.aliasEdge (slPrepared inp) raw).head =
      edge.head :=
    hheadEq.symm.trans hheadOrig
  have hmemTail : (Compound.aliasEdge (slPrepared inp) raw).tail ∈ comp := by
    apply slIdxMemOfLt
    rw [hcompTail]
    exact htailLt
  have hmemHead : (Compound.aliasEdge (slPrepared inp) raw).head ∈ comp := by
    apply slIdxMemOfLt
    rw [hcompHead]
    exact hheadLt
  have hsid : source.id = route.fromId := by
    rw [← hrouteEq]
    exact hsourceId
  have htid : target.id = route.toId := by
    rw [← hrouteEq]
    exact htargetId
  exact ⟨raw, source, target, hrawOf', hcompTail, hcompHead,
    slIdxLookup hmemTail, slIdxLookup hmemHead,
    hsource, hsid, htarget, htid⟩

/-- The model keys of an installed route name its input route's endpoints: the
installer's part is the selected component, the installed edge is the whole
chain, and the component keys at its ends index the route's source and target
boxes. Keys below the box count force aliased endpoints flat. -/
theorem SceneExecution.installed_route_end_keys (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1.1 candidate) execution.measured (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops with area := area })
    {route : ModelRoute}
    (hroute : inp.routes[key]? = some route) :
    ∃ (tailKey headKey : Nat) (hT : tailKey < inp.boxes.length)
      (hH : headKey < inp.boxes.length) (tailRect headRect : Rect),
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect ∧
      (inp.boxes[tailKey]'hT).id = route.fromId ∧
      (inp.boxes[headKey]'hH).id = route.toId := by
  have hinstC := hinst
  obtain ⟨qI, ctx0I, _, _, iI, eI, spanI, hmemI, hctxI, _, heI, hkeyI, _, _, hspanI,
    _⟩ := hinst
  obtain ⟨hcompEq, hq2, hidx⟩ :=
    execution.installed_edge_installer hinstC hselected hedge hdecl hrun hpart
      qI ctx0I iI eI hmemI hctxI heI hkeyI
  have hstraightC : (placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0I := by
    have hc := hctxI
    rw [hq2, hpart] at hc
    exact hc
  have hproperI : ctx0I.proper = run.proper := by
    have h1 := placeComponent_straighten_proper execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
    rw [hstraightC] at h1
    simpa using h1
  rw [hproperI] at heI
  have heI' : run.proper.edges[iI]? = some eI := heI
  have hmemRun : eI ∈ run.proper.edges := List.mem_of_getElem? heI'
  obtain ⟨eI', heI', heligI, _, _⟩ := straightSpanOf_inv hspanI
  have heIw : ctx0I.proper.edges[iI]? = some eI' := heI'
  rw [hproperI] at heIw
  have heqI : eI' = eI := Option.some.inj (heIw.symm.trans heI)
  rw [heqI] at heligI
  unfold straightEdgeEligible at heligI
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at heligI
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := heligI
  obtain ⟨tailNode, hvt, htd, htl, htb⟩ := straightRealNode_exists hTail
  obtain ⟨headNode, hvh, hhd, hhl, hhb⟩ := straightRealNode_exists hHead
  rw [hproperI] at hvt hvh
  obtain ⟨nT, hTailCg, _⟩ := installed_proper_cg_node hrun hvt htd htb
  obtain ⟨nH, hHeadCg, _⟩ := installed_proper_cg_node hrun hvh hhd hhb
  have hpos := execution.installed_edge_positions hinstC hselected hedge hdecl hrun hpart
    eI hmemRun hidx ⟨_, hTailCg⟩ ⟨_, hHeadCg⟩
  have hrev := execution.installed_edge_not_reversed hinstC hselected hedge hdecl hrun hpart
  obtain ⟨ranks, normalized, hn, _, _⟩ := srNormSrc hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hb := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length =
      q.1.1.length :=
    installed_comp_nodes_length _ _ _
  have hALt : edge.tail < q.1.1.length := by
    rw [← hlen]
    exact hb.1
  have hBLt : edge.head < q.1.1.length := by
    rw [← hlen]
    exact hb.2.1
  obtain ⟨raw, source, target, hrawOf', hcompTailM, hcompHeadM, htkM, hhkM, hsource,
    hsourceId, htarget, htargetId⟩ :=
    installed_route_model_keys execution.graph_eq (List.mem_of_getElem? hedge)
      hdecl hroute hrev hALt hBLt
  have htailLtE : eI.tail < q.1.1.length := by
    rw [← hlen]
    exact installed_proper_below hrun hvt htd htb
  have hheadLtE : eI.head < q.1.1.length := by
    rw [← hlen]
    exact installed_proper_below hrun hvh hhd hhb
  obtain ⟨tailKey, htk⟩ : ∃ k, q.1.1[eI.tail]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨htailLtE, rfl⟩⟩
  obtain ⟨headKey, hhk⟩ : ∃ k, q.1.1[eI.head]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨hheadLtE, rfl⟩⟩
  have htkA : q.1.1[q.1.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail]? =
      some tailKey := by
    rw [hcompTailM, ← hpos.1]
    exact htk
  have hhkA : q.1.1[q.1.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).head]? =
      some headKey := by
    rw [hcompHeadM, ← hpos.2]
    exact hhk
  have hmemTail : (Compound.aliasEdge (slPrepared inp) raw).tail ∈ q.1.1 := by
    apply slIdxMemOfLt
    rw [hcompTailM]
    exact hALt
  have hmemHead : (Compound.aliasEdge (slPrepared inp) raw).head ∈ q.1.1 := by
    apply slIdxMemOfLt
    rw [hcompHeadM]
    exact hBLt
  have htailKey : tailKey = (Compound.aliasEdge (slPrepared inp) raw).tail :=
    (Option.some.inj ((slIdxLookup hmemTail).symm.trans htkA)).symm
  have hheadKey : headKey = (Compound.aliasEdge (slPrepared inp) raw).head :=
    (Option.some.inj ((slIdxLookup hmemHead).symm.trans hhkA)).symm
  have hTmap : (Compound.aliasEdge (slPrepared inp) raw).tail =
      Compound.endpoint (slPrepared inp) true raw.tail raw.head := rfl
  have hHmap : (Compound.aliasEdge (slPrepared inp) raw).head =
      Compound.endpoint (slPrepared inp) false raw.head raw.tail := rfl
  have hPlen : (slPrepared inp).length = inp.boxes.length := by
    unfold slPrepared
    simp
  have hpartsEq := packAcc_parts_eq execution.packed_eq
  have hmemC : qI ∈ execution.componentsAcc.parts := by
    rwa [hpartsEq] at hmemI
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hparts, _⟩ := actual_components_parts hempty execution.components_eq
  have hcompI : qI.1 ∈ components execution.graph := by
    have h1 : qI.1 ∈ execution.componentsAcc.parts.map (·.1) :=
      List.mem_map_of_mem hmemC
    rwa [hparts] at h1
  have hcompQ : q.1.1 ∈ components execution.graph := by
    rw [← hcompEq]
    exact hcompI
  have hsmallT : tailKey < inp.boxes.length :=
    installed_key_lt_boxes execution hrun hvt htd htb hcompQ htk
  have hsmallH : headKey < inp.boxes.length :=
    installed_key_lt_boxes execution hrun hvh hhd hhb hcompQ hhk
  have heqT : tailKey = Compound.endpoint (slPrepared inp) true raw.tail raw.head := by
    rw [htailKey, hTmap]
  have heqH : headKey = Compound.endpoint (slPrepared inp) false raw.head raw.tail := by
    rw [hheadKey, hHmap]
  have hsmallT' : tailKey < (slPrepared inp).length := by
    rw [hPlen]
    exact hsmallT
  have hsmallH' : headKey < (slPrepared inp).length := by
    rw [hPlen]
    exact hsmallH
  have htailEq2 : tailKey = raw.tail :=
    endpoint_flat_of_bound heqT hsmallT'
  have hheadEq2 : headKey = raw.head :=
    endpoint_flat_of_bound heqH hsmallH'
  have hmidSize : execution.componentsAcc.rects.size = inp.boxes.length := by
    have hsz := installed_fold_rects_size execution.params inp o execution.graph execution.measured
      (components execution.graph) _ _ execution.components_eq
    rw [hsz]
    exact Array.size_replicate
  have hpackEq := execution.packed_eq
  unfold packAcc at hpackEq
  obtain ⟨packedB, hpackedB, hprestB⟩ := bind_ok hpackEq
  have hplen : execution.componentsAcc.parts.length = packedB.boxes.length := by
    have hcount := Pack.pack_count hpackedB
    rw [hcount, List.length_map]
  obtain ⟨cB, hcB⟩ := List.getElem?_of_mem hmemC
  have hcLtB : cB < packedB.boxes.length := by
    have h1 : cB < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hcB).1
    rw [hplen] at h1
    exact h1
  have hboxB : packedB.boxes[cB]? = some packedB.boxes[cB] :=
    List.getElem?_eq_some_iff.mpr ⟨hcLtB, rfl⟩
  have hselB : (execution.componentsAcc.parts.zip packedB.boxes)[cB]? =
      some (qI, packedB.boxes[cB]) :=
    List.getElem?_zip_eq_some.mpr ⟨hcB, hboxB⟩
  have hplaceI : qI.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area } := hq2.trans hpart
  have hrectsLen : qI.2.rects.length = q.1.1.length := by
    have h1 := installed_place_rects_length execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops
    have h2 := installed_comp_nodes_length execution.graph q.1.1 candidate
    rw [hplaceI, h1]
    exact h2
  have htkI : qI.1[eI.tail]? = some tailKey := by
    rw [hcompEq]
    exact htk
  have hhkI : qI.1[eI.head]? = some headKey := by
    rw [hcompEq]
    exact hhk
  have hRt : eI.tail < qI.2.rects.length := by
    rw [hrectsLen]
    exact htailLtE
  have hRh : eI.head < qI.2.rects.length := by
    rw [hrectsLen]
    exact hheadLtE
  obtain ⟨rectT, hrT⟩ : ∃ r, qI.2.rects[eI.tail]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRt⟩
  obtain ⟨rectH, hrH⟩ : ∃ r, qI.2.rects[eI.head]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRh⟩
  have hentryT : (qI.1.zip qI.2.rects)[eI.tail]? = some (tailKey, rectT) :=
    List.getElem?_zip_eq_some.mpr ⟨htkI, hrT⟩
  have hentryH : (qI.1.zip qI.2.rects)[eI.head]? = some (headKey, rectH) :=
    List.getElem?_zip_eq_some.mpr ⟨hhkI, hrH⟩
  have hsizeT_mid : tailKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact hsmallT
  have hsizeH_mid : headKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact hsmallH
  have hvalT := installed_packed_rect_value hempty execution.components_eq execution.packed_eq
    packedB hpackedB hselB hentryT hsizeT_mid default
  have hvalH := installed_packed_rect_value hempty execution.components_eq execution.packed_eq
    packedB hpackedB hselB hentryH hsizeH_mid default
  have hsizeT : tailKey < execution.packedAcc.rects.size := by
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_packAcc_rects_size execution.packed_eq).symm
    rw [← h2]
    exact hsmallT
  have hsizeH : headKey < execution.packedAcc.rects.size := by
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_packAcc_rects_size execution.packed_eq).symm
    rw [← h2]
    exact hsmallH
  have hlookT : execution.packedAcc.rects[tailKey]?
      = some (shiftRect (qI, packedB.boxes[cB]).2.x (qI, packedB.boxes[cB]).2.y rectT) := by
    have hne : execution.packedAcc.rects[tailKey]? ≠ none := by
      intro hcon
      exact absurd (Array.getElem?_eq_none_iff.mp hcon) (Nat.not_le_of_gt hsizeT)
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hne
    have h2 : ((execution.packedAcc.rects[tailKey]?).getD default)
        = shiftRect (qI, packedB.boxes[cB]).2.x (qI, packedB.boxes[cB]).2.y rectT := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalT
    have h3 : r = shiftRect (qI, packedB.boxes[cB]).2.x (qI, packedB.boxes[cB]).2.y rectT := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  have hlookH : execution.packedAcc.rects[headKey]?
      = some (shiftRect (qI, packedB.boxes[cB]).2.x (qI, packedB.boxes[cB]).2.y rectH) := by
    have hne : execution.packedAcc.rects[headKey]? ≠ none := by
      intro hcon
      exact absurd (Array.getElem?_eq_none_iff.mp hcon) (Nat.not_le_of_gt hsizeH)
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hne
    have h2 : ((execution.packedAcc.rects[headKey]?).getD default)
        = shiftRect (qI, packedB.boxes[cB]).2.x (qI, packedB.boxes[cB]).2.y rectH := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalH
    have h3 : r = shiftRect (qI, packedB.boxes[cB]).2.x (qI, packedB.boxes[cB]).2.y rectH := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  have hsrcGet : inp.boxes[tailKey]? = some source := by
    rw [htailEq2]
    exact hsource
  have htgtGet : inp.boxes[headKey]? = some target := by
    rw [hheadEq2]
    exact htarget
  have hsrcEq : source = inp.boxes[tailKey]'hsmallT :=
    Option.some.inj (hsrcGet.symm.trans (List.getElem?_eq_getElem hsmallT))
  have htgtEq : target = inp.boxes[headKey]'hsmallH :=
    Option.some.inj (htgtGet.symm.trans (List.getElem?_eq_getElem hsmallH))
  have hfrom : (inp.boxes[tailKey]'hsmallT).id = route.fromId := by
    rw [← hsrcEq]
    exact hsourceId
  have hto : (inp.boxes[headKey]'hsmallH).id = route.toId := by
    rw [← htgtEq]
    exact htargetId
  exact ⟨tailKey, headKey, hsmallT, hsmallH, _, _, hlookT, hlookH, hfrom, hto⟩
/-- The installed corridor's packed tail and head rectangles are exactly the
rectangles at this part's vertex keys: the installer's part is the selected
component, the installed edge is the whole chain, and the span is installed. -/
theorem SceneExecution.installed_part_edge_rects
    (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1.1 candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area }) :
    ∃ (tailKey headKey : Nat) (tailRect headRect : Rect) (span : StraightSpan),
      edge.tail < q.1.1.length ∧ edge.head < q.1.1.length ∧
      tailKey < inp.boxes.length ∧ headKey < inp.boxes.length ∧
      q.1.1[edge.tail]? = some tailKey ∧ q.1.1[edge.head]? = some headKey ∧
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect ∧
      0 ≤ tailRect.h ∧ 0 ≤ headRect.h ∧
      tailRect.x = span.tailRect.x ∧ tailRect.w = span.tailRect.w ∧
      headRect.x = span.headRect.x ∧ headRect.w = span.headRect.w ∧
      tailRect.x ≤ span.column ∧ span.column ≤ tailRect.x + tailRect.w ∧
      headRect.x ≤ span.column ∧ span.column ≤ headRect.x + headRect.w ∧
      span.top = tailRect.y + tailRect.h ∧ span.bottom = headRect.y ∧
      pts = span.points := by
  have hinstC := hinst
  obtain ⟨qI, ctx0I, oxI, oyI, iI, eI, spanI, hmemI, hctxI, hoffI, heI, hkeyI, _, _,
    hspanI, hptsI⟩ := hinst
  obtain ⟨hcompEq, hq2, hidx⟩ :=
    execution.installed_edge_installer hinstC hselected hedge hdecl hrun hpart
      qI ctx0I iI eI hmemI hctxI heI hkeyI
  have hstraightC : (placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0I := by
    have hc := hctxI
    rw [hq2, hpart] at hc
    exact hc
  have hproperI : ctx0I.proper = run.proper := by
    have h1 := placeComponent_straighten_proper execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
    rw [hstraightC] at h1
    simpa using h1
  have heI' : run.proper.edges[iI]? = some eI := by
    have h := heI
    rw [hproperI] at h
    exact h
  have hmemRun : eI ∈ run.proper.edges := List.mem_of_getElem? heI'
  obtain ⟨eI', heI', heligI, _, _⟩ := straightSpanOf_inv hspanI
  have heIw : ctx0I.proper.edges[iI]? = some eI' := heI'
  have heqI : eI' = eI := Option.some.inj (heIw.symm.trans heI)
  rw [heqI] at heligI
  unfold straightEdgeEligible at heligI
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at heligI
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := heligI
  obtain ⟨tailNode, hvt, htd, htl, htb⟩ := straightRealNode_exists hTail
  obtain ⟨headNode, hvh, hhd, hhl, hhb⟩ := straightRealNode_exists hHead
  rw [hproperI] at hvt hvh
  obtain ⟨nT, hTailCg, _⟩ := installed_proper_cg_node hrun hvt htd htb
  obtain ⟨nH, hHeadCg, _⟩ := installed_proper_cg_node hrun hvh hhd hhb
  have hpos := execution.installed_edge_positions hinstC hselected hedge hdecl hrun hpart
    eI hmemRun hidx ⟨_, hTailCg⟩ ⟨_, hHeadCg⟩
  obtain ⟨ranks, normalized, hn, _, _⟩ := srNormSrc hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hb := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length =
      q.1.1.length :=
    installed_comp_nodes_length _ _ _
  have hALt : edge.tail < q.1.1.length := by
    rw [← hlen]
    exact hb.1
  have hBLt : edge.head < q.1.1.length := by
    rw [← hlen]
    exact hb.2.1
  obtain ⟨tailKeyT, headKeyT, tailRectT, headRectT, hbtT, hbhT, htkT, hhkT, hlookT,
    hlookH, hthT, hhhT, htxT, htwT, hhxT, hhwT, htopT, hbotT⟩ :=
    installed_span_rect_transport_tied execution hmemI hctxI hoffI heI hspanI
  have hcol := straightSpanOf_column_mem hspanI
  have hcolT1 : tailRectT.x ≤ spanI.column := by
    rw [htxT]
    exact hcol.1
  have hcolT2 : spanI.column ≤ tailRectT.x + tailRectT.w := by
    rw [htxT, htwT]
    exact hcol.2.1
  have hcolH1 : headRectT.x ≤ spanI.column := by
    rw [hhxT]
    exact hcol.2.2.1
  have hcolH2 : spanI.column ≤ headRectT.x + headRectT.w := by
    rw [hhxT, hhwT]
    exact hcol.2.2.2
  have htkA : q.1.1[edge.tail]? = some tailKeyT := by
    have h1 := htkT
    rw [hcompEq, hpos.1] at h1
    exact h1
  have hhkA : q.1.1[edge.head]? = some headKeyT := by
    have h1 := hhkT
    rw [hcompEq, hpos.2] at h1
    exact h1
  have hpartsEq := packAcc_parts_eq execution.packed_eq
  have hmemC : qI ∈ execution.componentsAcc.parts := by
    rwa [hpartsEq] at hmemI
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hparts, _⟩ := actual_components_parts hempty execution.components_eq
  have hcompI : qI.1 ∈ components execution.graph := by
    have h1 : qI.1 ∈ execution.componentsAcc.parts.map (·.1) :=
      List.mem_map_of_mem hmemC
    rwa [hparts] at h1
  have hcompQ : q.1.1 ∈ components execution.graph := by
    rw [← hcompEq]
    exact hcompI
  have htkQ : q.1.1[eI.tail]? = some tailKeyT := by
    rw [← hcompEq]
    exact htkT
  have hhkQ : q.1.1[eI.head]? = some headKeyT := by
    rw [← hcompEq]
    exact hhkT
  have hsmallT : tailKeyT < inp.boxes.length :=
    installed_key_lt_boxes execution hrun hvt htd htb hcompQ htkQ
  have hsmallH : headKeyT < inp.boxes.length :=
    installed_key_lt_boxes execution hrun hvh hhd hhb hcompQ hhkQ
  exact ⟨tailKeyT, headKeyT, tailRectT, headRectT, spanI,
    hALt, hBLt, hsmallT, hsmallH, htkA, hhkA, hlookT, hlookH,
    hthT, hhhT, htxT, htwT, hhxT, hhwT, hcolT1, hcolT2, hcolH1, hcolH2,
    htopT, hbotT, hptsI⟩

/-- Membership in the global box list from packed and model lookups. -/
private theorem installed_global_mem {acc : Acc} {inp : Input} {vkey : Nat} {rect : Rect}
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
theorem installed_part_box_mem {inp : Input} {acc : Acc} {ctx0 : StraightenCtx}
    {comp : List Nat} {v k : Nat} {rect : Rect} {mbox : ModelBox}
    (hk : comp[v]? = some k) (hreal : straightRealNode ctx0.proper v = true)
    (hrect : acc.rects[k]? = some rect) (hbox : inp.boxes[k]? = some mbox)
    (hrole : ¬ mbox.role = BoxRole.node) :
    (true, rect) ∈ straightenPartBoxes inp acc ctx0 comp := by
  have hnot : ¬ (mbox.role == BoxRole.node) = true := fun h => hrole (beq_iff_eq.mp h)
  have hmemZ : (k, v) ∈ comp.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hk
  have hbeta : (fun q : Nat × Nat =>
      if straightRealNode ctx0.proper q.2 then
        match acc.rects[q.1]?, inp.boxes[q.1]? with
        | some r, some m => if m.role == BoxRole.node then none else some (true, r)
        | _, _ => none
      else none) (k, v) =
      if straightRealNode ctx0.proper v then
        match acc.rects[k]?, inp.boxes[k]? with
        | some r, some m => if m.role == BoxRole.node then none else some (true, r)
        | _, _ => none
      else none := rfl
  have hfun : (fun q : Nat × Nat =>
      if straightRealNode ctx0.proper q.2 then
        match acc.rects[q.1]?, inp.boxes[q.1]? with
        | some r, some m => if m.role == BoxRole.node then none else some (true, r)
        | _, _ => none
      else none) (k, v) = some (true, rect) := by
    rw [hbeta, ite_eq_left hreal, hrect, hbox]
    exact ite_eq_right hnot
  have hmem : (true, rect) ∈ comp.zipIdx.filterMap fun q : Nat × Nat =>
      if straightRealNode ctx0.proper q.2 then
        match acc.rects[q.1]?, inp.boxes[q.1]? with
        | some r, some m => if m.role == BoxRole.node then none else some (true, r)
        | _, _ => none
      else none :=
    List.mem_filterMap.mpr ⟨(k, v), hmemZ, hfun⟩
  unfold straightenPartBoxes
  exact List.mem_append.mpr (Or.inr hmem)

/-- A plain node's label survives coordinate construction: sizing, titling,
borders, and proxy clearing touch only geometry. -/
theorem coordinateGraph_plain_label (P : Params) {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraph P p).nodes[i]? = some out ∧
      out.label = nd.label ∧ out.edge = nd.edge ∧ out.node.border = 0 := by
  obtain ⟨sized, hs, hlabS, heS, hb'⟩ :
      ∃ sized, (sizeProperPorts P p).nodes[i]? = some sized ∧
        sized.label = nd.label ∧ sized.edge = nd.edge ∧ sized.node.border = 0 := by
    unfold sizeProperPorts
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, rfl, hb⟩
    · refine ⟨_, rfl, rfl, rfl, hb⟩
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have hlabT : (titleF sized).label = sized.label := by
    unfold titleF
    split <;> rfl
  have hedgeT : (titleF sized).edge = sized.edge := by
    unfold titleF
    split <;> rfl
  have hbT : (titleF sized).node.border = 0 := by
    have hkeep := (titleF_keys sized).2.1
    rw [hkeep]
    exact hb'
  have htitle : (titleReservations (sizeProperPorts P p)).nodes[i]? = some (titleF sized) := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp only [List.getElem?_map, hs, Option.map_some]
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[i]? =
      some (titleF sized) := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hcneg : ¬((titleF sized).node.border == -2 ||
      (titleF sized).node.border == 2) = true := by
    rw [hbT]
    decide
  have hclT : clearF (titleF sized) = titleF sized := by
    unfold clearF
    exact ite_eq_right hcneg
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[i]? =
      some (titleF sized) := by
    rw [clearProxyExtents_nodes]
    simp only [List.getElem?_map, hplaced, Option.map_some, hclT]
  have hlabX : (titleF sized).label = nd.label := hlabT.trans hlabS
  have hedgeX : (titleF sized).edge = nd.edge := hedgeT.trans heS
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · exact ⟨_, rfl, hlabX, hedgeX, hbT⟩
  · exact ⟨_, rfl, hlabX, hedgeX, hbT⟩

/-- Original component nodes keep their label flag through the whole run:
normalization records them exactly, label insertion only touches other nodes,
and coordinate construction preserves the flag. -/
private theorem componentRun_original_node_facts {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {gn : Node} (hcand : cg.nodes[v]? = some gn) (hbord : gn.border = 0) :
    ∃ out, run.proper.nodes[v]? = some out ∧ out.label = false ∧ out.node.border = 0 := by
  obtain ⟨ranks, p0, labeled, _, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec h
  have hnorm : p0.nodes[v]? = some (⟨gn, false, none, false⟩ : ProperNode) :=
    normalize_node_record hn hcand
  have hlab : labeled.nodes[v]? = some (⟨gn, false, none, false⟩ : ProperNode) :=
    addLabelNodes_untouched_node hl hnorm rfl
  obtain ⟨out, hout, hlabO, _, hbordO⟩ :=
    coordinateGraph_plain_label P hlab hbord
  rw [hcoord] at hout
  have houtP := componentRun_plain_node_dims h hout hbordO
  have hlabF : out.label = false := hlabO
  exact ⟨out, houtP, hlabF, hbordO⟩

/-- A component node that maps to a model box is not an edge-label node. -/
theorem SceneExecution.installed_component_node_not_label
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {v : Nat} {gn : Node}
    {run : Run} {nd : ProperNode}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hcand : (componentCandidate execution.graph comp candidate).nodes[v]? = some gn)
    (hbord : gn.border = 0)
    (hnd : run.proper.nodes[v]? = some nd) :
    nd.label = false := by
  obtain ⟨out, houtP, hlabF, _⟩ :=
    componentRun_original_node_facts hrun hcand hbord
  have heq : nd = out := Option.some.inj (hnd.symm.trans houtP)
  rw [heq]
  exact hlabF

/-- A real component node with a plain candidate box is a real straightening node. -/
theorem SceneExecution.installed_component_node_real
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {v : Nat} {gn : Node}
    {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hcand : (componentCandidate execution.graph comp candidate).nodes[v]? = some gn)
    (hbord : gn.border = 0)
    (hreal : RouteImpl.IsReal run.proper v) :
    straightRealNode run.proper v = true := by
  obtain ⟨out, houtP, hlabF, hbordO⟩ :=
    componentRun_original_node_facts hrun hcand hbord
  have hdum : out.dummy = false := hreal out houtP
  unfold straightRealNode
  simp only [houtP, hdum, hlabF, hbordO, Bool.not_false, beq_self_eq_true,
    Bool.true_and]


/-- A vertical corridor starting on a rectangle bottom edge misses it. -/
private theorem installed_corridor_misses_tail {c t b : Int} {r : Rect}
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

/-- A vertical corridor ending on a rectangle top edge misses it. -/
private theorem installed_corridor_misses_head {c t b : Int} {r : Rect}
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

/-- The route box ids for the keys of `installed_part_edge_rects`. -/
theorem SceneExecution.installed_part_edge_key_ids
    (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1.1 candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {route : ModelRoute}
    (hroute : inp.routes[key]? = some route)
    {tailKey headKey : Nat}
    (hT : tailKey < inp.boxes.length) (hH : headKey < inp.boxes.length) :
    q.1.1[edge.tail]? = some tailKey → q.1.1[edge.head]? = some headKey →
    (inp.boxes[tailKey]'hT).id = route.fromId ∧ (inp.boxes[headKey]'hH).id = route.toId := by
  have hinstC := hinst
  have hrev : edge.reversed = false :=
    execution.installed_edge_not_reversed hinstC hselected hedge hdecl hrun hpart
  obtain ⟨_ranks, _normalized, hn, _, _⟩ := srNormSrc hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hb := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length =
      q.1.1.length :=
    installed_comp_nodes_length _ _ _
  have hALt : edge.tail < q.1.1.length := by
    rw [← hlen]
    exact hb.1
  have hBLt : edge.head < q.1.1.length := by
    rw [← hlen]
    exact hb.2.1
  obtain ⟨raw, source, target, _hrawOf, hcompTailM, hcompHeadM, _htkM, _hhkM,
      hsource, hsourceId, htarget, htargetId⟩ :=
    installed_route_model_keys execution.graph_eq (List.mem_of_getElem? hedge)
      hdecl hroute hrev hALt hBLt
  intro htk hhk
  have hmemTail : (Compound.aliasEdge (slPrepared inp) raw).tail ∈ q.1.1 := by
    apply slIdxMemOfLt
    rw [hcompTailM]
    exact hALt
  have hmemHead : (Compound.aliasEdge (slPrepared inp) raw).head ∈ q.1.1 := by
    apply slIdxMemOfLt
    rw [hcompHeadM]
    exact hBLt
  have htkA : q.1.1[q.1.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).tail]? =
      some tailKey := by
    rw [hcompTailM]
    exact htk
  have hhkA : q.1.1[q.1.1.idxOf (Compound.aliasEdge (slPrepared inp) raw).head]? =
      some headKey := by
    rw [hcompHeadM]
    exact hhk
  have hlookupTail : q.1.1[q.1.1.idxOf
      (Compound.aliasEdge (slPrepared inp) raw).tail]? =
      some (Compound.aliasEdge (slPrepared inp) raw).tail :=
    slIdxLookup hmemTail
  have hlookupHead : q.1.1[q.1.1.idxOf
      (Compound.aliasEdge (slPrepared inp) raw).head]? =
      some (Compound.aliasEdge (slPrepared inp) raw).head :=
    slIdxLookup hmemHead
  have htailAlias : (Compound.aliasEdge (slPrepared inp) raw).tail = tailKey := by
    have h := hlookupTail.symm.trans htkA
    exact Option.some.inj h
  have hheadAlias : (Compound.aliasEdge (slPrepared inp) raw).head = headKey := by
    have h := hlookupHead.symm.trans hhkA
    exact Option.some.inj h
  have hTmap : (Compound.aliasEdge (slPrepared inp) raw).tail =
      Compound.endpoint (slPrepared inp) true raw.tail raw.head := rfl
  have hHmap : (Compound.aliasEdge (slPrepared inp) raw).head =
      Compound.endpoint (slPrepared inp) false raw.head raw.tail := rfl
  have hPlen : (slPrepared inp).length = inp.boxes.length := by
    unfold slPrepared
    simp
  have heqT : tailKey = Compound.endpoint (slPrepared inp) true raw.tail raw.head := by
    rw [← htailAlias, hTmap]
  have heqH : headKey = Compound.endpoint (slPrepared inp) false raw.head raw.tail := by
    rw [← hheadAlias, hHmap]
  have hsmallT : tailKey < (slPrepared inp).length := by
    rw [hPlen]
    exact hT
  have hsmallH : headKey < (slPrepared inp).length := by
    rw [hPlen]
    exact hH
  have htailEq : tailKey = raw.tail := endpoint_flat_of_bound heqT hsmallT
  have hheadEq : headKey = raw.head := endpoint_flat_of_bound heqH hsmallH
  have hsrcGet : inp.boxes[tailKey]? = some source := by
    rw [htailEq]
    exact hsource
  have htgtGet : inp.boxes[headKey]? = some target := by
    rw [hheadEq]
    exact htarget
  have hsrcEq : source = inp.boxes[tailKey]'hT :=
    Option.some.inj (hsrcGet.symm.trans (List.getElem?_eq_getElem hT))
  have htgtEq : target = inp.boxes[headKey]'hH :=
    Option.some.inj (htgtGet.symm.trans (List.getElem?_eq_getElem hH))
  have hfrom : (inp.boxes[tailKey]'hT).id = route.fromId := by
    rw [← hsrcEq]
    exact hsourceId
  have hto : (inp.boxes[headKey]'hH).id = route.toId := by
    rw [← htgtEq]
    exact htargetId
  exact ⟨hfrom, hto⟩

/-- An installed corridor misses every other node frame of its part. -/
theorem SceneExecution.installed_corridor_misses_other_frames
    (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point}
    {q : List Nat × Part} {ctx0 : StraightenCtx} {ox oy : Int} {i : Nat} {e : ProperEdge}
    {routing : Routing} {span : StraightSpan}
    (hmem : q ∈ execution.packedAcc.parts) (hctx : q.2.straighten = some ctx0)
    (hoff : straightenOffset q.1 q.2 execution.packedAcc.rects = some (ctx0, ox, oy))
    (he : ctx0.proper.edges[i]? = some e) (hdecl : e.decl = key)
    (hspan : straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing i =
      .ok (some span))
    (hpts : pts = span.points)
    (hclear : straightStepClear (straightenPartBoxes inp execution.packedAcc ctx0 q.1) span.tailRect
      span.headRect span.top span.bottom span.column = true)
    {packed : Pack.State} {c : Nat} {candidate : Nat} {j : Nat} {edge : Edge}
    {boxRect : Rect} (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (q, boxRect))
    (hedge : (componentCandidate execution.graph q.1 candidate).edges[j]? = some edge)
    (hjdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params (componentCandidate execution.graph q.1 candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    (hpart : q.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1 candidate) run 0 execution.measured loops
      with area := area }) :
    ∀ (v : Nat) (vkey : Nat) (rect : Rect) (mbox : ModelBox),
      v < q.1.length → q.1[v]? = some vkey → v ≠ edge.tail → v ≠ edge.head →
      inp.boxes[vkey]? = some mbox → mbox.role = BoxRole.node →
      execution.packedAcc.rects[vkey]? = some rect → 0 ≤ rect.h →
      ¬ Polyline.hitsRect pts rect := by
  have hne : e.tail ≠ e.head := by
    obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_inv hspan
    have heq : e' = e := Option.some.inj (he'.symm.trans he)
    rw [heq] at helig
    unfold straightEdgeEligible at helig
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hNe⟩, _⟩, _⟩ := helig
    intro hcon
    rw [hcon] at hNe
    simp at hNe
  have hinstC : Installed execution.packedAcc key pts :=
    ⟨q, ctx0, ox, oy, i, e, span, hmem, hctx, hoff, he, hdecl, hne, routing, hspan, hpts⟩
  have hrects :=
    execution.installed_part_edge_rects hinstC hselected hedge hjdecl hrun hpart
  obtain ⟨tailKeyT, headKeyT, tailRectT, headRectT, spanT, hTailLt, hHeadLt, hKeyTB,
      hKeyHB, htkA, hhkA, hlookT, hlookH, hthT, hhhT, htxT, htwT, hhxT, hhwT, hcolT1,
      hcolT2, hcolH1, hcolH2, htopT, hbotT, hptsT⟩ := hrects
  have hptsEqT : pts = [⟨spanT.column, spanT.top⟩, ⟨spanT.column, spanT.bottom⟩] :=
    hptsT.trans rfl
  obtain ⟨qI, ctx0I, oxI, oyI, iI, eI, spanI, hmemI, hctxI, hoffI, heI, hkeyI, hneI,
      routingI, hspanI, hptsI⟩ := hinstC
  have hltI : spanI.top < spanI.bottom := straightSpanOf_top_lt hspanI
  have hptsEqI : pts = [⟨spanI.column, spanI.top⟩, ⟨spanI.column, spanI.bottom⟩] :=
    hptsI.trans rfl
  have hlistEq : ([⟨spanT.column, spanT.top⟩, ⟨spanT.column, spanT.bottom⟩] : List Point) =
      ([⟨spanI.column, spanI.top⟩, ⟨spanI.column, spanI.bottom⟩] : List Point) :=
    hptsEqT.symm.trans hptsEqI
  have hfirst : (⟨spanT.column, spanT.top⟩ : Point) = ⟨spanI.column, spanI.top⟩ := by
    have h0 := congrArg List.head? hlistEq
    exact Option.some.inj h0
  have hsecond : (⟨spanT.column, spanT.bottom⟩ : Point) =
      ⟨spanI.column, spanI.bottom⟩ := by
    have h1 := congrArg (fun l : List Point => l[1]?) hlistEq
    exact Option.some.inj h1
  have htopEq : spanT.top = spanI.top := congrArg Point.y hfirst
  have hbotEq : spanT.bottom = spanI.bottom := congrArg Point.y hsecond
  have hltTB : spanT.top < spanT.bottom := by
    rw [htopEq, hbotEq]
    exact hltI
  have hshape : span.top = span.tailRect.y + span.tailRect.h ∧
      span.bottom = span.headRect.y := by
    have hspan2 := hspan
    unfold straightSpanOf at hspan2
    cases he2 : ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper.edges[i]? with
    | none =>
      simp only [he2] at hspan2
      cases hspan2
    | some e2 =>
      simp only [he2] at hspan2
      cases hel : !straightEdgeEligible { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
        routing i e2 with
      | true =>
        simp only [hel] at hspan2
        cases hspan2
      | false =>
        simp only [hel] at hspan2
        cases hgeom : straightGeom { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
          routing i e2 with
        | mk tw hw th hh tailLeft headLeft lo hi cx =>
          simp only [hgeom] at hspan2
          by_cases hlo : lo > hi
          · rw [ite_eq_left hlo] at hspan2
            cases hspan2
          · rw [ite_eq_right hlo] at hspan2
            obtain ⟨pin, _, hspan2⟩ := bind_ok hspan2
            obtain ⟨top, _, hspan2⟩ := bind_ok hspan2
            obtain ⟨bottom, _, hspan2⟩ := bind_ok hspan2
            by_cases hge : top ≥ bottom
            · rw [ite_eq_left hge] at hspan2
              cases hspan2
            · rw [ite_eq_right hge] at hspan2
              obtain ⟨column, _, hspan2⟩ := bind_ok hspan2
              have hs := Option.some.inj (Except.ok.inj hspan2)
              subst hs
              refine ⟨by dsimp only; omega, by dsimp only⟩
  have hptsEq : pts = [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] :=
    hpts.trans rfl
  have hlt : span.top < span.bottom := straightSpanOf_top_lt hspan
  intro v vkey rect mbox hv hkey hneT hneH hbox hrole hlook _h00
  have hmem := installed_global_mem hlook hbox
  have hflag : decide (mbox.role == BoxRole.node) = true := by
    have hb : (mbox.role == BoxRole.node) = true := by
      rw [hrole]
      exact beq_self_eq_true _
    rw [decide_eq_true_eq]
    exact hb
  have hcond := List.all_eq_true.mp hclear _ (List.mem_append.mpr (Or.inl hmem))
  have hcondBeta : (rect == span.tailRect || rect == span.headRect ||
      !(decide (mbox.role == BoxRole.node)) ||
      !Polyline.hitsRectB [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩]
        rect) = true := hcond
  cases hEqT : rect == span.tailRect with
  | true =>
    have hRectEqT : rect = span.tailRect := beq_iff_eq.mp hEqT
    have hmissTail := installed_corridor_misses_tail (c := span.column) hshape.1 hlt
    have hgoalT : ¬ Polyline.hitsRect pts rect := by
      rw [hptsEq, hRectEqT]
      exact hmissTail
    exact hgoalT
  | false =>
    cases hEqH : rect == span.headRect with
    | true =>
      have hRectEqH : rect = span.headRect := beq_iff_eq.mp hEqH
      have hmissHead := installed_corridor_misses_head (c := span.column) hshape.2 hlt
      have hgoalH : ¬ Polyline.hitsRect pts rect := by
        rw [hptsEq, hRectEqH]
        exact hmissHead
      exact hgoalH
    | false =>
      cases hFlagB : (decide (mbox.role == BoxRole.node)) with
      | true =>
        cases hB : Polyline.hitsRectB [⟨span.column, span.top⟩,
            ⟨span.column, span.bottom⟩] rect with
        | true =>
          have hNotFlag : (!(decide (mbox.role == BoxRole.node))) = false := by
            rw [hFlagB]
            exact Bool.not_true
          have hNotB : (!Polyline.hitsRectB [⟨span.column, span.top⟩,
              ⟨span.column, span.bottom⟩] rect) = false := by
            rw [hB]
            exact Bool.not_true
          rw [hEqT, hEqH, hNotFlag, hNotB] at hcondBeta
          cases hcondBeta
        | false =>
          have hBpts : Polyline.hitsRectB pts rect = false := by
            rw [hptsEq]
            exact hB
          exact (Polyline.hitsRectB_eq_false_iff _ _).mp hBpts
      | false =>
        have hcon : (true : Bool) = false := hflag.symm.trans hFlagB
        cases hcon
/-- An installed corridor misses every other box of its own part that is an
    obstacle: a node box, or the box of a real proper node. -/
theorem SceneExecution.installed_corridor_misses_part_boxes
    (execution : SceneExecution inp o res)
    {key : Nat} {pts : List Point}
    {q : List Nat × Part} {ctx0 : StraightenCtx} {ox oy : Int} {i : Nat} {e : ProperEdge}
    {routing : Routing} {span : StraightSpan}
    (_hmem : q ∈ execution.packedAcc.parts) (_hctx : q.2.straighten = some ctx0)
    (_hoff : straightenOffset q.1 q.2 execution.packedAcc.rects = some (ctx0, ox, oy))
    (he : ctx0.proper.edges[i]? = some e) (_hdecl : e.decl = key)
    (hspan : straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing i =
      .ok (some span))
    (hpts : pts = span.points)
    (hclear : straightStepClear (straightenPartBoxes inp execution.packedAcc ctx0 q.1) span.tailRect
      span.headRect span.top span.bottom span.column = true) :
    ∀ (v : Nat) (vkey : Nat) (rect : Rect),
      q.1[v]? = some vkey → v ≠ e.tail → v ≠ e.head →
      execution.packedAcc.rects[vkey]? = some rect → 0 ≤ rect.h →
      ((∃ mbox, inp.boxes[vkey]? = some mbox ∧ mbox.role = BoxRole.node) ∨
        straightRealNode ctx0.proper v = true) →
      ¬ Polyline.hitsRect pts rect := by
  have hne : e.tail ≠ e.head := by
    obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_inv hspan
    have heq : e' = e := Option.some.inj (he'.symm.trans he)
    rw [heq] at helig
    unfold straightEdgeEligible at helig
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hNe⟩, _⟩, _⟩ := helig
    intro hcon
    rw [hcon] at hNe
    simp at hNe
  have hptsEq : pts = [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] :=
    hpts.trans rfl
  have hlt : span.top < span.bottom := straightSpanOf_top_lt hspan
  have hshape : span.top = span.tailRect.y + span.tailRect.h ∧
      span.bottom = span.headRect.y := by
    have hspan2 := hspan
    unfold straightSpanOf at hspan2
    cases he2 : ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper.edges[i]? with
    | none =>
      simp only [he2] at hspan2
      cases hspan2
    | some e2 =>
      simp only [he2] at hspan2
      cases hel : !straightEdgeEligible { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
        routing i e2 with
      | true =>
        simp only [hel] at hspan2
        cases hspan2
      | false =>
        simp only [hel] at hspan2
        cases hgeom : straightGeom { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
          routing i e2 with
        | mk tw hw th hh tailLeft headLeft lo hi cx =>
          simp only [hgeom] at hspan2
          by_cases hlo : lo > hi
          · rw [ite_eq_left hlo] at hspan2
            cases hspan2
          · rw [ite_eq_right hlo] at hspan2
            obtain ⟨pin, _, hspan2⟩ := bind_ok hspan2
            obtain ⟨top, _, hspan2⟩ := bind_ok hspan2
            obtain ⟨bottom, _, hspan2⟩ := bind_ok hspan2
            by_cases hge : top ≥ bottom
            · rw [ite_eq_left hge] at hspan2
              cases hspan2
            · rw [ite_eq_right hge] at hspan2
              obtain ⟨column, _, hspan2⟩ := bind_ok hspan2
              have hs := Option.some.inj (Except.ok.inj hspan2)
              subst hs
              refine ⟨by dsimp only; omega, by dsimp only⟩
  have htail_head_hit : ∀ (r : Rect), (r == span.tailRect || r == span.headRect || false ||
      !Polyline.hitsRectB [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩]
        r) = true → ¬ Polyline.hitsRect pts r := by
    intro r hcondBeta
    cases hEqT : r == span.tailRect with
    | true =>
      have hRectEqT : r = span.tailRect := beq_iff_eq.mp hEqT
      have hmissTail := installed_corridor_misses_tail (c := span.column) hshape.1 hlt
      have hgoalT : ¬ Polyline.hitsRect pts r := by
        rw [hptsEq, hRectEqT]
        exact hmissTail
      exact hgoalT
    | false =>
      cases hEqH : r == span.headRect with
      | true =>
        have hRectEqH : r = span.headRect := beq_iff_eq.mp hEqH
        have hmissHead := installed_corridor_misses_head (c := span.column) hshape.2 hlt
        have hgoalH : ¬ Polyline.hitsRect pts r := by
          rw [hptsEq, hRectEqH]
          exact hmissHead
        exact hgoalH
      | false =>
        cases hB : Polyline.hitsRectB [⟨span.column, span.top⟩,
            ⟨span.column, span.bottom⟩] r with
        | true =>
          rw [hEqT, hEqH, hB] at hcondBeta
          cases hcondBeta
        | false =>
          have hBpts : Polyline.hitsRectB pts r = false := by
            rw [hptsEq]
            exact hB
          exact (Polyline.hitsRectB_eq_false_iff _ _).mp hBpts
  intro v vkey rect hkey hneT hneH hlook _hpos hor
  rcases hor with ⟨mbox, hboxM, hroleM⟩ | hreal
  · have hflag : decide (mbox.role == BoxRole.node) = true := by
      have hb : (mbox.role == BoxRole.node) = true := by
        rw [hroleM]
        exact beq_self_eq_true _
      rw [decide_eq_true_eq]
      exact hb
    have hmemG := installed_global_mem hlook hboxM
    rw [hflag] at hmemG
    have hcond := List.all_eq_true.mp hclear _ (List.mem_append.mpr (Or.inl hmemG))
    have hcondBeta : (rect == span.tailRect || rect == span.headRect || false ||
        !Polyline.hitsRectB [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩]
          rect) = true := hcond
    exact htail_head_hit rect hcondBeta
  · have hmidSize : execution.componentsAcc.rects.size = inp.boxes.length := by
      have hsz := installed_fold_rects_size execution.params inp o execution.graph execution.measured
        (components execution.graph) _ _ execution.components_eq
      rw [hsz]
      exact Array.size_replicate
    obtain ⟨hltR, _⟩ := Array.getElem?_eq_some_iff.mp hlook
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_packAcc_rects_size execution.packed_eq).symm
    have hvlen : vkey < inp.boxes.length := by omega
    have hbox : inp.boxes[vkey]? = some (inp.boxes[vkey]'hvlen) :=
      List.getElem?_eq_getElem hvlen
    by_cases hrole : (inp.boxes[vkey]'hvlen).role = BoxRole.node
    · have hflag : decide ((inp.boxes[vkey]'hvlen).role == BoxRole.node) = true := by
        have hb : ((inp.boxes[vkey]'hvlen).role == BoxRole.node) = true := by
          rw [hrole]
          exact beq_self_eq_true _
        rw [decide_eq_true_eq]
        exact hb
      have hmemG := installed_global_mem hlook hbox
      rw [hflag] at hmemG
      have hcond := List.all_eq_true.mp hclear _ (List.mem_append.mpr (Or.inl hmemG))
      have hcondBeta : (rect == span.tailRect || rect == span.headRect || false ||
          !Polyline.hitsRectB [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩]
            rect) = true := hcond
      exact htail_head_hit rect hcondBeta
    · have hmemP := installed_part_box_mem hkey hreal hlook hbox hrole
      have hcond := List.all_eq_true.mp hclear _ hmemP
      have hcondBeta : (rect == span.tailRect || rect == span.headRect || false ||
          !Polyline.hitsRectB [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩]
            rect) = true := hcond
      exact htail_head_hit rect hcondBeta


end PipelineImpl
end Layered
end Elegant
