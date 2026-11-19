import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem marker_mapM_record {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      xs.length = ys.length ∧
      ∀ (i : Nat) (y : β), ys[i]? = some y →
        ∃ x, xs[i]? = some x ∧ f x = .ok y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    change Except.ok [] = Except.ok ys at h
    injection h with heq
    subst ys
    refine ⟨rfl, ?_⟩
    intro i y hy
    simp at hy
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    cases hf : f x with
    | error e =>
      rw [hf] at h
      change Except.error e = Except.ok ys at h
      cases h
    | ok y =>
      cases ht : xs.mapM f with
      | error e =>
        rw [hf, ht] at h
        change Except.error e = Except.ok ys at h
        cases h
      | ok tail =>
        rw [hf, ht] at h
        change Except.ok (y :: tail) = Except.ok ys at h
        injection h with heq
        subst ys
        obtain ⟨hlen, hget⟩ := ih tail ht
        refine ⟨by simp [hlen], ?_⟩
        intro i z hz
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
          subst z
          exact ⟨x, rfl, hf⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hz
          obtain ⟨a, ha, he⟩ := hget i z hz
          exact ⟨a, by simpa using ha, he⟩

private theorem marker_sizedNodes_metadata {P : Params}
    {lines : List (List Measure.Line)} {nodes : List Node}
    (h : sizedNodes P lines = .ok nodes) :
    nodes.length = lines.length ∧
      ∀ (i : Nat) (n : Node), nodes[i]? = some n → n.decl = i ∧ n.border = 0 := by
  unfold sizedNodes at h
  obtain ⟨hlen, hget⟩ := marker_mapM_record
    (fun (q : List Measure.Line × Nat) => sizedNode P q.2 q.1)
    lines.zipIdx nodes h
  refine ⟨by simpa using hlen.symm, ?_⟩
  intro i n hn
  obtain ⟨q, hq, hs⟩ := hget i n hn
  have hi : i < lines.length := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hq
    simpa using hi
  have hqi : q.2 = i := by
    have hq' : lines.zipIdx[i]? = some (lines[i], i) := by simp [hi]
    rw [hq] at hq'
    exact congrArg Prod.snd (Option.some.inj hq')
  unfold sizedNode at hs
  cases hh : nodeSize P q.1 with
  | error e =>
    rw [hh] at hs
    change Except.error e = Except.ok n at hs
    cases hs
  | ok size =>
    rw [hh] at hs
    change Except.ok { decl := q.2, w := size.1, h := size.2, loopExtent := 0 } =
      Except.ok n at hs
    injection hs with heq
    subst n
    exact ⟨hqi, rfl⟩

theorem prepare_paired_markers (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (source : Graph) {i : Nat}
    (hi : i < source.nodes.length) {box : ModelBox}
    (hbox : boxes[i]? = some box) (hgroup : box.role = .group)
    (hdecl : source.nodes[i].decl = i) :
    ∃ top bottom : Node,
      (Compound.prepare boxes pad titles source).nodes[i]? = some top ∧
      bottom ∈ (Compound.prepare boxes pad titles source).nodes ∧
      top.border = -2 ∧ bottom.border = 2 ∧
      top.decl = i ∧ bottom.decl = i ∧
      top.clusterPath = Compound.path boxes box ++ [i] ∧
      bottom.clusterPath = top.clusterPath ∧ bottom.w = 0 ∧ bottom.h = 0 := by
  let top : Node := { source.nodes[i] with
    clusterPath := Compound.path boxes box ++ [i]
    border := -2
    w := (titles.getD i (0, 0)).1
    h := if source.nodes[i].loopExtent == 0 then (titles.getD i (0, 0)).2 + pad
         else max ((titles.getD i (0, 0)).2 + pad) source.nodes[i].h }
  let bottom : Node := {
    decl := i
    w := 0
    h := 0
    clusterPath := Compound.path boxes box ++ [i]
    border := 2 }
  refine ⟨top, bottom, ?_, ?_, rfl, rfl, hdecl, rfl, rfl, rfl, rfl, rfl⟩
  · exact Compound.prepare_group_title_record boxes pad titles source hi hbox hgroup
  · exact Compound.prepare_bottom_exists boxes pad titles source hbox hgroup

theorem measuredGraph_prepared_source {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) :
    ∃ (nodes : List Node) (edges : List Edge) (titles : List (Int × Int)),
      g = Compound.prepare (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
        P.clusterPad titles { nodes := nodes, edges := edges, slot := P.slot } ∧
      nodes.length = lines.length ∧
      ∀ (i : Nat) (n : Node), nodes[i]? = some n → n.decl = i ∧ n.border = 0 := by
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hg' := Except.ok.inj hg
  obtain ⟨hlen, hinit⟩ := marker_sizedNodes_metadata hinitial
  obtain ⟨hprocessed, hget⟩ := marker_mapM_record _ _ _ hnodes
  refine ⟨nodes, edges, _, hg'.symm, ?_, ?_⟩
  · simpa [hlen] using hprocessed.symm
  · intro i n hn
    obtain ⟨before, hbefore, hstep⟩ := hget i n hn
    have hi : i < initial.length := by
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hbefore
      simpa using hi
    have hbeforeEq : before = (orientNode o.direction initial[i], i) := by
      have he : ((initial.map (orientNode o.direction)).zipIdx)[i]? =
          some (orientNode o.direction initial[i], i) := by simp [hi]
      rw [hbefore] at he
      exact Option.some.inj he
    subst before
    have hmeta := hinit i initial[i] (by simp [hi])
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · simp at hstep
    · split at hstep <;> (try split at hstep) <;>
        (try split at hstep) <;> (try split at hstep) <;>
        first
        | (have he := Except.ok.inj hstep
           rw [← he]
           cases o.direction <;> simpa [orientNode] using hmeta)
        | (simp [throw, throwThe, MonadExceptOf.throw] at hstep)

theorem measuredGraph_paired_markers {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) {i : Nat}
    (hi : i < lines.length) {box : ModelBox}
    (hbox : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[i]? = some box)
    (hgroup : box.role = .group) :
    ∃ top bottom : Node,
      g.nodes[i]? = some top ∧ bottom ∈ g.nodes ∧
      top.border = -2 ∧ bottom.border = 2 ∧
      top.decl = i ∧ bottom.decl = i ∧
      top.clusterPath = Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) box ++ [i] ∧
      bottom.clusterPath = top.clusterPath ∧ bottom.w = 0 ∧ bottom.h = 0 := by
  obtain ⟨nodes, edges, titles, hprepare, hlen, hmetadata⟩ :=
    measuredGraph_prepared_source hg
  have hin : i < nodes.length := by omega
  have hdecl := (hmetadata i nodes[i] (by simp [hin])).1
  rw [hprepare]
  exact prepare_paired_markers _ _ _ _ hin hbox hgroup hdecl


end Elegant.Layered.PipelineImpl
