import Elegant.Layered.ExactPartBounded

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Copy of the private `mapM_index_record`: index-wise preimage of a
successful `mapM`. -/
private theorem X_mapM_index_record {α β : Type} (f : α → Except LayoutError β) :
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

/-- Copy of the private `sizedNodes_index_metadata`: sized nodes keep their
declaration index and start with a plain border. -/
private theorem X_sizedNodes_index_metadata {P : Params}
    {lines : List (List Measure.Line)} {nodes : List Node}
    (h : sizedNodes P lines = .ok nodes) :
    nodes.length = lines.length ∧
      ∀ (i : Nat) (n : Node), nodes[i]? = some n → n.decl = i ∧ n.border = 0 := by
  unfold sizedNodes at h
  obtain ⟨hlen, hget⟩ := X_mapM_index_record
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

/-- Copy of the private `measuredGraph_title_metadata`: a `border = -2` node
of the measured graph is the actual title node of the group box at its index,
which therefore carries no fixed-size entry. -/
private theorem X_measuredGraph_title_metadata {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g) {j : Nat} {top : Node}
    (htop : g.nodes[j]? = some top) (hborder : top.border = -2) :
    j < lines.length ∧ top.decl = j ∧
      ∃ box, inp.boxes[j]? = some box ∧ box.role = .group ∧
        inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false ∧
        top.w = (match o.direction with
          | .LR | .RL => (max 1 (lines.getD j []).length : Int) * P.lineH
          | .TB | .BT => (lines.getD j []).foldl (fun w line => max w line.width) 0) ∧
        (match o.direction with
          | .LR | .RL => (lines.getD j []).foldl (fun w line => max w line.width) 0
          | .TB | .BT => (max 1 (lines.getD j []).length : Int) * P.lineH) +
            P.clusterPad ≤ top.h := by
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hg' := Except.ok.inj hg
  subst g
  obtain ⟨hlen, hinit⟩ := X_sizedNodes_index_metadata hinitial
  obtain ⟨hprocessed, hget⟩ := X_mapM_index_record _ _ _ hnodes
  have hnodeslen : nodes.length = lines.length := by simpa [hlen] using hprocessed.symm
  have hj : j < nodes.length := by
    by_cases hj : j < nodes.length
    · exact hj
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ j (by dsimp only; omega) htop
      omega
  obtain ⟨before, hbefore, hstep⟩ := hget j (nodes[j]) (by simp [hj])
  have hjinit : j < initial.length := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hbefore
    simpa using hi
  have hbeforeEq : before = (orientNode o.direction initial[j], j) := by
    have he : ((initial.map (orientNode o.direction)).zipIdx)[j]? =
        some (orientNode o.direction initial[j], j) := by simp [hjinit]
    rw [hbefore] at he
    exact Option.some.inj he
  subst before
  have hmeta := hinit j initial[j] (by simp [hjinit])
  have hz : nodes[j].decl = j ∧ nodes[j].border = 0 := by
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
  obtain ⟨box, hb, hrole, hdecl, hw, hh, _, _⟩ :=
    Compound.prepare_group_title_of_border _ _ _ _ hj htop hborder
      (by dsimp only; rw [hz.2]; decide)
  cases horiginal : inp.boxes[j]? with
  | none => simp [List.getElem?_map, horiginal] at hb
  | some original =>
    simp only [List.getElem?_map, horiginal, Option.map_some, Option.some.injEq] at hb
    have heq := hb
    have hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == original.id) = false := by
      cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == original.id) with
      | false => rfl
      | true =>
        have hr := hrole
        rw [← heq] at hr
        simp [hf] at hr
    have hbox : original = box := by simpa [hfixed] using heq
    clear hb heq
    subst box
    have hjlines : j < lines.length := by omega
    refine ⟨hjlines, hdecl.trans hz.1, original, rfl, hrole, hfixed, ?_, ?_⟩
    · cases hd : o.direction <;>
        simpa [List.getD, List.getElem?_map, hjlines, hd] using hw
    · cases hd : o.direction <;>
        simpa [List.getD, List.getElem?_map, hjlines, hd] using hh

 /-- A successful exact graph keeps every group-title node: titles carry no
 fixed size, because groups with fixed sizes are plain nodes in the measured
 graph, and an exact id without a fixed size is a domain error. -/
 theorem exactGraph_border2_unchangedX {P : Params} {exactIds : List String} {inp : Input}
     {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
     {g0 g : Graph} (hg0 : measuredGraph P inp o lines = .ok g0)
     (h : exactGraph P exactIds inp o measured g0 = .ok g)
     {j : Nat} {top0 : Node} (h0 : g0.nodes[j]? = some top0)
     (hb : top0.border = -2) : g.nodes[j]? = some top0 := by
   obtain ⟨_, hdecl, box, hbox, _, hfixed, _, _⟩ :=
     X_measuredGraph_title_metadata hg0 h0 hb
   have hin : inp.boxes[top0.decl]? = some box := by
     rw [hdecl]
     exact hbox
   have hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
     List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
   unfold exactGraph at h
   obtain ⟨nodes, hnodes, h⟩ := bind_ok h
   have he := Except.ok.inj h
   subst he
   obtain ⟨nd', hnd', hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 j top0 h0
   simp only [hin] at hnd'
   split at hnd'
   · have hred : top0 = nd' :=
       Except.ok.inj (by simpa only [pure, Except.pure] using hnd')
     subst hred
     exact hmem
   · rw [hfind] at hnd'
     dsimp only at hnd'
     cases hnd'

 /-- Discharge the `exactGraph` residual for executed exact layouts. -/
 theorem exactBorder2Unchanged_discharge {exactIds : List String} {inp : Input}
     {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res) :
     ExactBorder2Unchanged execution := by
   intro j top0 h0 hb
   exact exactGraph_border2_unchangedX execution.graph0_eq execution.graph_eq h0 hb

 /-- Every exact component part is bounded by its part dimensions, with no
 residual hypothesis. -/
 theorem exactPartsBounded' {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
     ∀ q ∈ execution.componentsAcc.parts, PartBounded q.2 :=
   exactPartsBounded execution (exactBorder2Unchanged_discharge execution)

end PipelineImpl
end Layered
end Elegant
