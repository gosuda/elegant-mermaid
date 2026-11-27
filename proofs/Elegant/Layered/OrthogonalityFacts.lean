import Elegant.Layered.SceneBounds
import Elegant.Layered.RouteTransport

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Elegant.Layered.PipelineImpl

private theorem mapM_all_result {α β : Type} (f : α → Except LayoutError β)
    (Q : β → Prop) (hf : ∀ a b, f a = .ok b → Q b) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ y ∈ ys, Q y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    have he : [] = ys := Except.ok.inj h
    subst ys
    simp
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨rest, hr, h⟩ := bind_ok h
    have he : y :: rest = ys := Except.ok.inj h
    subst ys
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hf x z hy
    · exact ih rest hr z hz

private theorem zip_right_mem {α β : Type} :
    ∀ (xs : List α) (ys : List β) (q : α × β), q ∈ xs.zip ys → q.2 ∈ ys := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro ys q h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ys q h)

 theorem componentRun_routes_orthogonal {P : Params} (hP : P.Valid)
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hs : CgShape cg)
    (h : componentRun P cg labels orderOptions = .ok run) :
    ∀ rt ∈ run.routes, Polyline.isOrthogonal rt.points = true := by
  have hshape := (componentRun_facts hP hd hs h).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, _, _, hpoints⟩ := componentRun_spec h
  exact Layered.route_orthogonal hshape hr hpoints

 theorem componentRun_edgePoints_orthogonal {P : Params} (hP : P.Valid)
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hs : CgShape cg)
    (h : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) (hi : i < cg.edges.length) :
    Polyline.isOrthogonal (edgePoints run i cg.edges[i]) = true := by
  rw [componentRun_edgePoints_of_index h hi]
  exact componentRun_routes_orthogonal hP hd hs h _ (List.getElem_mem _)

private theorem loops_orthogonal {node : Rect} {slot : Int} {labels : List LoopLabel}
    {out : List LoopPlacement} (h : Loops.loops node slot labels = .ok out) :
    ∀ q ∈ out, Polyline.isOrthogonal q.points = true := by
  unfold Loops.loops at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · have he := Except.ok.inj h
          subst out
          intro q hq
          obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hq
          exact Loops.placement_orthogonal _ _ _ _ _ _
        · contradiction

private theorem exactLoops_orthogonal {node : Rect} {slot : Int} {labels : List LoopLabel}
    {out : List LoopPlacement} (h : Loops.exactLoops node slot labels = .ok out) :
    ∀ q ∈ out, Polyline.isOrthogonal q.points = true := by
  unfold Loops.exactLoops at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · have he := Except.ok.inj h
          subst out
          intro q hq
          obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hq
          simp [Loops.exactPlacement, Polyline.isOrthogonal,
            Polyline.isOrthogonal_cons]
        · contradiction

 theorem componentLoops_orthogonal {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    (h : componentLoops P cg run labels = .ok loops) :
    ∀ q ∈ loops, Polyline.isOrthogonal q.2.points = true := by
  unfold componentLoops at h
  obtain ⟨groups, hgroups, h⟩ := bind_ok h
  have he : groups.flatten = loops := Except.ok.inj h
  subst loops
  have hall : ∀ group ∈ groups,
      ∀ q ∈ group, Polyline.isOrthogonal q.2.points = true := by
    apply mapM_all_result _ (fun group : List (Nat × LoopPlacement) =>
      ∀ q ∈ group, Polyline.isOrthogonal q.2.points = true) ?_ _ _ hgroups
    intro v group hg
    obtain ⟨out, hout, hg⟩ := bind_ok hg
    have he := Except.ok.inj hg
    subst group
    intro q hq
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hq
    have hm := zip_right_mem _ _ entry hentry
    split at hout
    · exact exactLoops_orthogonal hout entry.2 hm
    · exact loops_orthogonal hout entry.2 hm
  intro q hq
  obtain ⟨group, hg, hq⟩ := List.mem_flatten.mp hq
  exact hall group hg q hq

 theorem placeComponent_routes_orthogonal {P : Params} (hP : P.Valid)
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {loops : List (Nat × LoopPlacement)}
    (hd : (cg.edges.map (·.decl)).Nodup) (hs : CgShape cg)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hloops : componentLoops P cg run labels = .ok loops) (cursor : Int) :
    ∀ q ∈ (placeComponent P cg run cursor labels loops).routes,
      Polyline.isOrthogonal q.2 = true := by
  intro q hq
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hq
  apply (Layered.isOrthogonal_shift _ _ _).mpr
  cases hf : loops.find? (fun l => l.1 == entry.1.decl) with
  | some loop =>
    simpa only [hf, Option.map_some, Option.getD_some] using
      componentLoops_orthogonal hloops loop (List.mem_of_find?_eq_some hf)
  | none =>
    simp only [Option.map_none, Option.getD_none]
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp hentry)
    rw [← he]
    exact componentRun_edgePoints_orthogonal hP hd hs hrun _ hi

private def RoutesOrthogonal (a : Array (List Point)) : Prop :=
  ∀ k, Polyline.isOrthogonal (a.getD k []) = true

private theorem routes_fold_orthogonal (entries : List (Nat × List Point))
    (f : List Point → List Point)
    (hf : ∀ points, Polyline.isOrthogonal points = true →
      Polyline.isOrthogonal (f points) = true)
    (he : ∀ q ∈ entries, Polyline.isOrthogonal q.2 = true)
    (a : Array (List Point)) (ha : RoutesOrthogonal a) :
    RoutesOrthogonal (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a) := by
  induction entries generalizing a with
  | nil => exact ha
  | cons q rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun r hr => he r (List.mem_cons_of_mem _ hr))
    intro k
    rw [RankImpl.getD_set!]
    split
    · exact hf q.2 (he q List.mem_cons_self)
    · exact ha k

private theorem placePart_routes_orthogonal {P : Params} (hP : P.Valid)
    {comp : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {acc out : Acc}
    (hd : (cg.edges.map (·.decl)).Nodup) (hs : CgShape cg)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (ha : RoutesOrthogonal acc.routes)
    (h : placePart comp cg run P acc labels = .ok out) :
    RoutesOrthogonal out.routes := by
  unfold placePart at h
  obtain ⟨loops, hloops, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp at h
  · have he := Except.ok.inj h
    subst out
    exact routes_fold_orthogonal _ id (fun _ h => h)
      (placeComponent_routes_orthogonal hP hd hs hrun hloops 0) _ ha

private theorem layoutComponent_routes_orthogonal {P : Params} (hP : P.Valid)
    {inp : Input} {o : Options} {g : Graph} {comp : List Nat}
    {labels : List MeasuredLabel} {acc out : Acc}
    (hd : (g.edges.map (·.decl)).Nodup) (hs : CgShape g) (hcomp : comp.Nodup)
    (ha : RoutesOrthogonal acc.routes)
    (h : layoutComponent P inp o g acc comp labels = .ok out) :
    RoutesOrthogonal out.routes := by
  unfold layoutComponent at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨index, trial, _, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrial at ht
  obtain ⟨run, hrun, ht⟩ := bind_ok ht
  obtain ⟨_, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  rw [hv] at hp
  have hplaced := placePart_routes_orthogonal hP
    (componentCandidate_decls_nodup g comp index hd)
    (componentCandidate_shape hcomp hs index) hrun ha hp
  have he := Except.ok.inj h
  subst out
  exact hplaced

private theorem components_routes_orthogonal {P : Params} (hP : P.Valid)
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel}
    (hd : (g.edges.map (·.decl)).Nodup) (hs : CgShape g) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      (∀ comp ∈ comps, comp.Nodup) → RoutesOrthogonal start.routes →
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out →
      RoutesOrthogonal out.routes := by
  intro comps
  induction comps with
  | nil =>
    intro start out _ ha h
    have he : start = out := Except.ok.inj h
    subst out
    exact ha
  | cons comp comps ih =>
    intro start out hcomps ha h
    simp only [List.foldlM_cons] at h
    obtain ⟨mid, hm, h⟩ := bind_ok h
    apply ih mid out (fun c hc => hcomps c (List.mem_cons_of_mem _ hc))
    · exact layoutComponent_routes_orthogonal hP hd hs
        (hcomps comp List.mem_cons_self) ha hm
    · exact h

private theorem packAcc_routes_orthogonal {P : Params} {o : Options} {acc out : Acc}
    (ha : RoutesOrthogonal acc.routes)
    (hparts : ∀ q ∈ acc.parts, ∀ route ∈ q.2.routes,
      Polyline.isOrthogonal route.2 = true)
    (h : packAcc P o acc = .ok out) : RoutesOrthogonal out.routes := by
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst out
  rw [packAcc_routes_eq_foldl]
  have hpairs : ∀ q ∈ acc.parts.zip packed.boxes,
      ∀ route ∈ q.1.2.routes, Polyline.isOrthogonal route.2 = true := by
    intro q hq
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hq
    exact hparts q.1 (List.mem_of_getElem? (zip_getElem?_left hk))
  have preserve : ∀ (pairs : List ((List Nat × Part) × Rect)) (a : Array (List Point)),
      (∀ q ∈ pairs, ∀ route ∈ q.1.2.routes,
        Polyline.isOrthogonal route.2 = true) →
      RoutesOrthogonal a →
      RoutesOrthogonal (pairs.foldl (fun arr q => q.1.2.routes.foldl
        (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) arr) a) := by
    intro pairs
    induction pairs with
    | nil => intro a _ ha; exact ha
    | cons q pairs ih =>
      intro a hpairs ha
      simp only [List.foldl_cons]
      apply ih _ (fun r hr => hpairs r (List.mem_cons_of_mem _ hr))
      exact routes_fold_orthogonal _ _
        (fun points h => (Layered.isOrthogonal_shift _ _ points).mpr h)
        (hpairs q List.mem_cons_self) _ ha
  exact preserve _ _ hpairs ha

 theorem SceneExecution.routes_orthogonal {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ route ∈ res.scene.routes, Polyline.isOrthogonal route.points = true := by
  have hP := checkedParams_valid execution.checked
  have hd := measuredGraph_decls_nodup execution.graph_eq
  have hs := measuredGraph_shape execution.graph_eq
  have hinit : RoutesOrthogonal (Array.replicate inp.routes.length ([] : List Point)) := by
    intro k
    simp [Array.getD, Polyline.isOrthogonal]
  have hmid := components_routes_orthogonal hP hd hs _ _ _
    (components_nodup execution.graph) hinit execution.components_eq
  have hparts : ∀ q ∈ execution.componentsAcc.parts,
      ∀ route ∈ q.2.routes, Polyline.isOrthogonal route.2 = true := by
    obtain ⟨hm, hall⟩ := actual_components_parts rfl execution.components_eq
    intro q hq
    have hcomp : q.1 ∈ components execution.graph := by
      rw [← hm]
      exact List.mem_map_of_mem hq
    obtain ⟨index, _, run, loops, _, _, _, hrun, hloops, hroutes⟩ := hall q hq
    rw [hroutes]
    exact placeComponent_routes_orthogonal hP
      (componentCandidate_decls_nodup _ _ index hd)
      (componentCandidate_shape (components_nodup _ _ hcomp) hs index)
      hrun hloops 0
  have hpacked := packAcc_routes_orthogonal hmid hparts execution.packed_eq
  have hstart : ∀ (j : Nat) (pts : List Point), execution.packedAcc.routes[j]? = some pts →
      Polyline.isOrthogonal pts = true := by
    intro j pts hj
    have hget : execution.packedAcc.routes.getD j [] = pts := by
      rw [Array.getD_eq_getD_getElem?, hj, Option.getD_some]
    rw [← hget]
    exact hpacked j
  have hstraight := straightenAcc_routes_orthogonal execution.straight_eq hstart
  have hstraightD : ∀ k, Polyline.isOrthogonal (execution.straightAcc.routes.getD k []) = true := by
    intro k
    cases hget : execution.straightAcc.routes[k]? with
    | none =>
      rw [Array.getD_eq_getD_getElem?, hget, Option.getD_none]
      rfl
    | some pts =>
      rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
      exact hstraight k pts hget
  rw [execution.scene_eq]
  intro route hroute
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hroute
  exact (Layered.isOrthogonal_shift_orient _ _ _ _ _).mpr (hstraightD q.2)

theorem SceneExecution.c4 {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : Validator.C4 res.scene.layoutDump := by
  intro route hroute _
  exact execution.routes_orthogonal route hroute

theorem layout_c4 {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) : Validator.C4 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layout_sceneExecution h
  exact execution.c4

end Elegant.Layered.PipelineImpl

namespace Elegant.Layered.PipelineImpl

theorem expandChild_routes_orthogonal {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleHeight : Int} {parent child out : FamilyResult}
    (hp : ∀ route ∈ parent.scene.routes, Polyline.isOrthogonal route.points = true)
    (hc : ∀ route ∈ child.scene.routes, Polyline.isOrthogonal route.points = true)
    (h : expandChild P inp o group titleHeight parent child = .ok out) :
    ∀ route ∈ out.scene.routes, Polyline.isOrthogonal route.points = true := by
  unfold expandChild at h
  cases hframe : parent.scene.boxes.find? (fun box => box.id == group.id) with
  | none =>
    simp only [hframe] at h
    contradiction
  | some frame =>
    simp only [hframe] at h
    obtain ⟨frame', hframe', h⟩ := bind_ok h
    have heframe : frame = frame' := Except.ok.inj hframe'
    subst frame'
    obtain ⟨metric, _, h⟩ := bind_ok h
    obtain ⟨titleLines, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    have he := Except.ok.inj h
    subst out
    intro route hroute
    obtain ⟨model, _, hfind⟩ := List.mem_filterMap.mp hroute
    have hmem := List.mem_of_find?_eq_some hfind
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨original, horiginal, he⟩ := List.mem_map.mp hmem
      rw [← he]
      exact (Layered.isOrthogonal_shift _ _ _).mpr (hc original horiginal)
    · exact hp route hmem

theorem layoutRecursive_routes_orthogonal :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res →
      ∀ route ∈ res.scene.routes, Polyline.isOrthogonal route.points = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h
    obtain ⟨execution⟩ := layout_sceneExecution h
    exact execution.routes_orthogonal
  | succ fuel ih =>
    intro inp o res h
    cases hg : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
    | none =>
      simp only [layoutRecursive, hg] at h
      obtain ⟨execution⟩ := layout_sceneExecution h
      exact execution.routes_orthogonal
    | some group =>
      simp only [layoutRecursive, hg] at h
      obtain ⟨P, _, h⟩ := bind_ok h
      obtain ⟨metric, _, h⟩ := bind_ok h
      obtain ⟨child, hchild, h⟩ := bind_ok h
      obtain ⟨titleLines, _, h⟩ := bind_ok h
      obtain ⟨parent, hparent, h⟩ := bind_ok h
      exact expandChild_routes_orthogonal
        (ih _ _ parent hparent) (ih _ _ child hchild) h

theorem layoutRecursive_c4 {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRecursive fuel inp o = .ok res) :
    Validator.C4 res.scene.layoutDump := by
  intro route hroute _
  exact layoutRecursive_routes_orthogonal fuel inp o res h route hroute

end Elegant.Layered.PipelineImpl

namespace Elegant.Layered

theorem layoutFamily_c4 {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) :
    Validator.C4 res.scene.layoutDump := by
  exact PipelineImpl.layoutRecursive_c4 (layoutFamily_success h).2

end Elegant.Layered
