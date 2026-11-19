import Elegant.Chart.TreemapFacts

namespace Elegant.Treemap.Containment

theorem wellFormed_boxIdsDistinct {m : Model} (hwf : WellFormed m) :
    boxIdsDistinct m = true :=
  decide_eq_true (Model.boxIds_nodup hwf)

theorem find_box_eq_map (nodes : List Node) (boxes : List ModelBox)
    (hboxes : boxes = nodes.map Node.source) (id : String) :
    boxes.find? (fun b : ModelBox => b.id == id) =
      (nodes.find? (fun n : Node => n.source.id == id)).map Node.source := by
  rw [hboxes, List.find?_map]
  rfl

theorem parentChainEnds_mono (boxes : List ModelBox) :
    ∀ fuel n id, fuel ≤ n → parentChainEnds boxes fuel id = true →
      parentChainEnds boxes n id = true := by
  intro fuel n
  induction n generalizing fuel with
  | zero =>
    intro id hle h
    cases fuel with
    | zero => exact h
    | succ k => exact absurd hle (Nat.not_succ_le_zero k)
  | succ n ih =>
    intro id hle h
    by_cases he : id = ""
    · subst he; exact rfl
    · cases fuel with
      | zero =>
        have hfalse : parentChainEnds boxes 0 id = false := by
          rw [parentChainEnds.eq_2 boxes id (by intro h; exact he h)]
        rw [hfalse] at h
        exact absurd h (by decide)
      | succ k =>
        have hkle : k ≤ n := Nat.le_of_succ_le_succ hle
        cases hf : boxes.find? (fun b : ModelBox => b.id == id) with
        | none =>
          rw [parentChainEnds.eq_3 boxes id k he, hf] at h
          simp at h
          rw [parentChainEnds.eq_3 boxes id n he, hf]
        | some b =>
          rw [parentChainEnds.eq_3 boxes id k he, hf] at h
          have h' : parentChainEnds boxes k b.parent = true := h
          rw [parentChainEnds.eq_3 boxes id n he, hf]
          exact ih k b.parent hkle h'

theorem depthProfile_parentChainEnds (nodes : List Node) (boxes : List ModelBox)
    (hboxes : boxes = nodes.map Node.source) :
    ∀ (d : Nat) (id : String), CanvasC1.DepthProfile nodes id d →
      parentChainEnds boxes (d + 1) id = true := by
  intro d
  induction d with
  | zero =>
    intro id hprof
    by_cases hid : id = ""
    · subst id; rfl
    · cases hf : nodes.find? (fun x : Node => x.source.id == id) with
      | none =>
        have hcorr : boxes.find? (fun b : ModelBox => b.id == id) = none := by
          rw [find_box_eq_map nodes boxes hboxes id, hf]
          rfl
        rw [parentChainEnds.eq_3 boxes id 0 hid, hcorr]
      | some n =>
        have h2 := hprof 1
        simp [parentDepth, hf] at h2
  | succ d ih =>
    intro id hprof
    by_cases hid : id = ""
    · subst id; rfl
    · cases hf : nodes.find? (fun x : Node => x.source.id == id) with
      | none =>
        have hnez : parentDepth nodes (d + 1 + 1) id = d + 1 := by
          have := hprof (d + 1 + 1)
          simpa using this
        simp [parentDepth, hf] at hnez
      | some n =>
        have hstep : ∀ fuel, parentDepth nodes (fuel + 1) id =
            1 + parentDepth nodes fuel n.source.parent := by
          intro fuel
          simp [parentDepth, hf]
        have hprof' : CanvasC1.DepthProfile nodes n.source.parent d := by
          intro fuel
          have hs := hprof (fuel + 1)
          rw [hstep fuel] at hs
          omega
        have hcorr : boxes.find? (fun b : ModelBox => b.id == id) = some n.source := by
          rw [find_box_eq_map nodes boxes hboxes id, hf]
          rfl
        rw [parentChainEnds.eq_3 boxes id (d + 1) hid, hcorr]
        exact ih n.source.parent hprof'

theorem wellFormed_parentChainsEnd {m : Model} (hwf : WellFormed m) :
    parentChainsEnd m = true := by
  have hsrc : (initialNodes m).map Node.source = m.boxes :=
    CanvasC1.initialNodes_source m
  have hlenEq : (initialNodes m).length = m.boxes.length := by
    simpa using congrArg List.length hsrc
  unfold parentChainsEnd
  apply List.all_eq_true.mpr
  intro box hbox
  obtain ⟨depth, hprof⟩ :=
    CanvasC1.source_parent_depthProfile m hwf (initialNodes m) hsrc box hbox
  have hpos : 0 < m.boxes.length := List.length_pos_of_mem hbox
  have hk : m.boxes.length = m.boxes.length - 1 + 1 := by omega
  have hlt := CanvasC1.source_parent_depth_lt_length m hwf (initialNodes m) hsrc box hbox
  rw [hprof (initialNodes m).length, hlenEq] at hlt
  have hdepth : depth < m.boxes.length := by omega
  rw [hk]
  refine parentChainEnds_mono m.boxes (depth + 1) (m.boxes.length - 1 + 1) box.parent
    (by omega) ?_
  exact depthProfile_parentChainEnds (initialNodes m) m.boxes hsrc.symm depth box.parent
    hprof

/-! ### Native-shaped titled treemap admission and kept-guard witnesses -/

/-- The native titled treemap model, transcribed from
    `bin/emd-go layout --stage model --profile vector` of the source
    `treemap-beta` / `title My Title` / `"A"` / `  "B": 5` / `  "C": 3`
    (the parent's aggregate lifts `n0`'s value to `8`, the sum of its
    children's `5` and `3`). -/
def titledModel : Model := {
  kind := "treemap",
  profile := .vector,
  boxes := [{ id := "root", role := .group, parent := "", exclusive := false, direction := "" },
            { id := "n0", role := .group, parent := "root", exclusive := false, direction := "" },
            { id := "n1", role := .node, parent := "n0", exclusive := false },
            { id := "n2", role := .node, parent := "n0", exclusive := false }],
  routes := [],
  labels := [{ id := "title", owner := "root", text := "My Title" },
             { id := "n0.name", owner := "n0", text := "A" },
             { id := "n0.value", owner := "n0", text := "8" },
             { id := "n1.name", owner := "n1", text := "B" },
             { id := "n1.value", owner := "n1", text := "5" },
             { id := "n2.name", owner := "n2", text := "C" },
             { id := "n2.value", owner := "n2", text := "3" }],
  regionSets := [{ parent := 0, regions := [0, 0, 5000, 3000] }] }

theorem titled_treemap_label_ids_admitted :
    labelIdsNameOwner titledModel = true := by
  unfold labelIdsNameOwner
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  decide

theorem c7RootOwnerWitness_rejected :
    Kinds.Treemap.layout C7Counterexample.c7RootOwnerWitness =
      .error (.geometry .domain) := by
  rfl

theorem emptyIdWitness_rejected :
    Kinds.Treemap.layout EmptyIdCounterexample.emptyIdWitness =
      .error (.geometry .domain) := by
  rfl


/-- `hwf` gives chain termination on box parents. -/
theorem wellFormed_parentChainEnds {m : Model} (hwf : WellFormed m)
    (b : ModelBox) (hb : b ∈ m.boxes) :
    parentChainEnds m.boxes m.boxes.length b.parent = true := by
  have hall := List.all_eq_true.mp (wellFormed_parentChainsEnd hwf) b hb
  exact hall

/-- No box is its own parent: a self-loop would make `parentTerminates` run out
    of fuel, contradicting well-formedness. -/
theorem modelBox_parent_ne_id {m : Model} (hwf : WellFormed m) (c : ModelBox)
    (hc : c ∈ m.boxes) (hid : c.id ≠ "") : c.parent ≠ c.id := by
  have hmain : ∀ b ∈ m.boxes,
      (∀ x : ModelBox, x ∈ m.boxes → x.parent = b.parent →
        x.id = "" ∨ x.id ≠ b.parent) := by
    intro b hb
    refine Elegant.parent_induction m hwf
      (fun id => ∀ x : ModelBox, x ∈ m.boxes → x.parent = id →
        x.id = "" ∨ x.id ≠ id) ?_ ?_ b hb
    · intro x _ _
      by_cases hx0 : x.id = ""
      · exact Or.inl hx0
      · exact Or.inr hx0
    · intro box hbox hIH x hx hpar
      by_cases hx0 : x.id = ""
      · exact Or.inl hx0
      · right
        intro hself
        have hxb : x = box := TileForest.nodup_boxes_id_inj
          (Model.boxIds_nodup hwf) hx hbox hself
        cases hxb
        rcases hIH box hbox rfl with h0 | hne
        · exact absurd h0 hx0
        · exact hne hpar.symm
  rcases hmain c hc c hc rfl with h | h
  · intro _; exact hid h
  · intro hpc; exact h hpc.symm

/-- Node-level form: sources are the box list, so no node is its own parent.
    Requires the adapter's nonempty-id admission. -/
theorem nodes_parent_ne_id {m : Model} (hwf : WellFormed m) (nodes0 : List Node)
    (hsources : nodes0.map Node.source = m.boxes)
    (_hnodup : (nodes0.map (fun n => n.source.id)).Nodup)
    (hid : ∀ n ∈ nodes0, n.source.id ≠ "") :
    ∀ n ∈ nodes0, n.source.parent ≠ n.source.id := by
  intro n hn hself
  have hbox : n.source ∈ m.boxes := by
    rw [← hsources]
    exact List.mem_map.mpr ⟨n, hn, rfl⟩
  exact modelBox_parent_ne_id hwf n.source hbox (hid n hn) hself

/-- The per-index C3 fact: whenever the node at index `k` is the parent of the
    node at index `bIdx`, the `k` rectangle contains the `bIdx` rectangle. -/
def RectIdxId (acc : List Node) (k bIdx : Nat) : Prop :=
  ∀ b : Node, acc[bIdx]? = some b → b.source.parent ≠ "" →
    ∀ old : Node, acc[k]? = some old → old.source.id = b.source.parent →
      Rect.Contained (tileRect old.rect) (tileRect b.rect)

/-- Every processed index satisfies `RectIdxId`. -/
def ProcessedContained (acc : List Node) (done : List Nat) : Prop :=
  ∀ k ∈ done, ∀ bIdx, RectIdxId acc k bIdx

/-! ### C3: parent containment through the `tileNodes` fold -/

section C3

/-- Pointwise-equal functions give equal maps. -/
theorem map_eq_of_pointwise {α β : Type} {f g : α → β} (l : List α)
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy)), h x (by simp)]

/-- Two indices of a nodup list carrying the same element are equal. -/
theorem getElem?_pos_eq {α : Type} {l : List α} (hn : l.Nodup) {i j : Nat}
    {a : α} (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hi
  exact (List.Nodup.getElem?_inj hbound hn).mp (hi.trans hj.symm)

/-- Two indices of a node list with distinct source ids are equal when the
    looked-up nodes share their source id. -/
theorem acc_index_eq_of_id_eq {acc : List Node}
    (hnodup : (acc.map (fun n => n.source.id)).Nodup) {k i : Nat} {a b : Node}
    (hk : acc[k]? = some a) (hi : acc[i]? = some b)
    (hid : a.source.id = b.source.id) : k = i := by
  have hk' : (acc.map (fun n => n.source.id))[k]? = some a.source.id := by
    rw [List.getElem?_map, hk, Option.map_some]
  have hi' : (acc.map (fun n => n.source.id))[i]? = some b.source.id := by
    rw [List.getElem?_map, hi, Option.map_some]
  obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hk'
  rw [hid] at hk'
  exact (List.Nodup.getElem?_inj hbound hnodup).mp (hk'.trans hi'.symm)

/-- When the node list is unchanged by a step and the step's index has no
    lookup, processed containment extends to the appended index. -/
theorem processed_keep_none {acc mid : List Node} {done : List Nat} {i : Nat}
    (hEq : mid = acc) (hi : acc[i]? = none) (hdone : ProcessedContained acc done) :
    ProcessedContained mid (done ++ [i]) := by
  subst hEq
  intro k hk bIdx b hb hne old hold heq
  rcases List.mem_append.mp hk with hk | hk
  · exact hdone k hk bIdx b hb hne old hold heq
  · have hkeq : k = i := List.mem_singleton.mp hk
    subst hkeq
    rw [hi] at hold
    simp at hold

set_option maxHeartbeats 1600000 in
/-- The per-step C3 fact: one `tileStep` extends `ProcessedContained` from the
    processed prefix `done` to `done ++ [i]`. -/
theorem tileStep_contained {m : Model} (hwf : WellFormed m) (nodes0 : List Node)
    (hsources0 : nodes0.map Node.source = m.boxes)
    (hid0 : ∀ n ∈ nodes0, n.source.id ≠ "")
    (hself0 : ∀ n ∈ nodes0, n.source.parent ≠ n.source.id)
    {c : Consts} {acc mid : List Node} {i : Nat} {done rest : List Nat}
    (hsources_acc : acc.map Node.source = nodes0.map Node.source)
    (hnodup_acc : (acc.map (fun n => n.source.id)).Nodup)
    (hordered_acc : ∀ n ∈ acc, n.rect.Ordered)
    (hdone : ProcessedContained acc done)
    (hord_step : done ++ i :: rest = dependencyOrder nodes0)
    (hstep : CanvasC1.tileStep c acc i = .ok mid) :
    ProcessedContained mid (done ++ [i]) := by
  have hordnodup : (dependencyOrder nodes0).Nodup :=
    CanvasC1.dependencyOrder_index_nodup nodes0
  have hi_pos : (dependencyOrder nodes0)[done.length]? = some i := by
    rw [← hord_step]; simp
  have hi_fresh : i ∉ done := by
    intro hmem
    obtain ⟨pos, hposb, hpose⟩ := List.mem_iff_getElem.mp hmem
    have hpos : done[pos]? = some i :=
      List.getElem?_eq_some_iff.mpr ⟨hposb, hpose⟩
    have hposord : (dependencyOrder nodes0)[pos]? = some i := by
      rw [← hord_step, List.getElem?_append_left hposb, hpos]
    have hEq := getElem?_pos_eq hordnodup hposord hi_pos
    omega
  have hi_mem : i ∈ dependencyOrder nodes0 := by
    rw [← hord_step]; simp
  obtain ⟨inode, hinode0⟩ := CanvasC1.dependencyOrder_index_source nodes0 i hi_mem
  obtain ⟨accnode, haccnode0, hsrcacc⟩ :=
    CanvasC1.source_lookup_of_map_eq acc nodes0 hsources_acc.symm i inode hinode0
  cases hi_acc : acc[i]? with
  | none =>
    simp only [CanvasC1.tileStep, hi_acc, Except.ok.injEq, pure, Except.pure] at hstep
    exact processed_keep_none hstep.symm hi_acc hdone
  | some parent =>
    have hsrcparent : parent.source = inode.source := by
      have hEq : accnode = parent := Option.some.inj (haccnode0.symm.trans hi_acc)
      rw [hEq] at hsrcacc
      exact hsrcacc
    by_cases hchildren : (sortedChildren acc parent.source.id).isEmpty = true
    · simp only [CanvasC1.tileStep, hi_acc, hchildren, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hstep
      subst hstep
      intro k hk bIdx b hb hne old hold heq
      rcases List.mem_append.mp hk with hk | hk
      · exact hdone k hk bIdx b hb hne old hold heq
      · have hkeq : k = i := List.mem_singleton.mp hk
        subst hkeq
        rw [hi_acc] at hold
        have holdE : parent = old := Option.some.inj hold
        rw [holdE.symm] at heq ⊢
        -- b has a parent, so it must be in sortedChildren; the list is empty.
        have hpar : b.source.parent = parent.source.id := heq.symm
        have hmemIdx : bIdx ∈ sortedChildren acc parent.source.id :=
          CanvasC1.sortedChildren_mem_of_lookup acc parent.source.id bIdx b hb hpar
        rw [List.isEmpty_iff.mp hchildren] at hmemIdx
        exact absurd hmemIdx List.not_mem_nil
    · have hchildren' : (sortedChildren acc parent.source.id).isEmpty = false := by
        cases hv : (sortedChildren acc parent.source.id).isEmpty <;> simp_all
      obtain ⟨cells, capped, hsq, hout, _hdisj⟩ :=
        CanvasC1.tileStep_children_execution c acc mid i parent hi_acc hchildren'
          (hordered_acc parent (List.mem_of_getElem? hi_acc)) hstep
      have hzlen : cells.length = (sortedChildren acc parent.source.id).length := by
        simpa only [List.length_map] using
          squarify_length _ _ _ _ cells capped hsq
      have hbOut : ∀ j, (∀ q ∈ (sortedChildren acc parent.source.id).zip cells,
          q.1 ≠ j) → mid[j]? = acc[j]? := by
        intro j hj
        rw [hout]
        exact CanvasC1.batch_getElem?_outside acc
          ((sortedChildren acc parent.source.id).zip cells) c.innerX c.innerY j hj
      -- Processed indices are never among the assignments of this step: their
      -- parent (the node at `i`) precedes them in the dependency order.
      have hdoneFresh : ∀ j ∈ done,
          ∀ q ∈ (sortedChildren acc parent.source.id).zip cells, q.1 ≠ j := by
        intro j hj q hq hq1
        exfalso
        obtain ⟨n0, hn0mem, hn0par⟩ := CanvasC1.sortedChildren_index_source acc
          parent.source.id q.1 (List.of_mem_zip hq).1
        have hjmem : j ∈ dependencyOrder nodes0 := by
          rw [← hord_step]; exact List.mem_append_left _ hj
        obtain ⟨cnode0, hcnode0⟩ :=
          CanvasC1.dependencyOrder_index_source nodes0 j hjmem
        obtain ⟨accnodej, haccnodej0, hsrcj⟩ :=
          CanvasC1.source_lookup_of_map_eq acc nodes0 hsources_acc.symm j cnode0
            hcnode0
        have hq1' : q.1 = j := hq1
        have hn0mem' : acc[j]? = some n0 := by
          rw [← hq1']; exact hn0mem
        have hEqn : n0 = accnodej := Option.some.inj (hn0mem'.symm.trans haccnodej0)
        have hjpar : accnodej.source.parent = parent.source.id := by
          rw [← hEqn]; exact hn0par
        have hjpar0 : cnode0.source.parent = inode.source.id := by
          rw [← hsrcj, ← hsrcparent]
          exact hjpar
        obtain ⟨posj, hposjb, hposje⟩ := List.mem_iff_getElem.mp hj
        have hposj : (dependencyOrder nodes0)[posj]? = some j := by
          rw [← hord_step, List.getElem?_append_left hposjb]
          exact List.getElem?_eq_some_iff.mpr ⟨hposjb, hposje⟩
        have hlt := CanvasC1.dependencyOrder_parent_before_child m hwf nodes0
          hsources0 done.length posj i j inode cnode0 hi_pos hposj hinode0 hcnode0
          hjpar0 (hid0 inode (List.mem_of_getElem? hinode0))
        omega
      have hinot : ∀ q ∈ (sortedChildren acc parent.source.id).zip cells,
          q.1 ≠ i := by
        intro q hq hqi
        obtain ⟨n0, hn0mem, hn0par⟩ := CanvasC1.sortedChildren_index_source acc
          parent.source.id q.1 (List.of_mem_zip hq).1
        have hqi' : q.1 = i := hqi
        have hn0mem' : acc[i]? = some n0 := by
          rw [← hqi']; exact hn0mem
        have hEqn : n0 = parent := Option.some.inj (hn0mem'.symm.trans hi_acc)
        rw [hEqn] at hn0par
        have hfinal : inode.source.parent = inode.source.id := by
          rw [← hsrcparent]
          exact hn0par
        exact hself0 inode (List.mem_of_getElem? hinode0) hfinal
      have hi_mid : mid[i]? = some parent := by
        rw [hbOut i hinot]
        exact hi_acc
      intro k hk bIdx b hb hne old hold heq
      rcases List.mem_append.mp hk with hk | hk
      · -- `k ∈ done`: its rectangle and its children's rectangles survive.
        have hko : mid[k]? = acc[k]? := hbOut k (hdoneFresh k hk)
        rw [hko] at hold
        by_cases hass : bIdx ∈
            ((sortedChildren acc parent.source.id).zip cells).map Prod.fst
        · exfalso
          obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hass
          cases q with
          | mk j _ =>
            have hqb : j = bIdx := hq1
            have hbmem : bIdx ∈ sortedChildren acc parent.source.id := by
              have h1 := (List.of_mem_zip hq).1
              rwa [hqb] at h1
            obtain ⟨n0, hn0mem, hn0par⟩ := CanvasC1.sortedChildren_index_source acc
              parent.source.id bIdx hbmem
            have hbSrc : b.source = n0.source := by
              have h := congrArg (fun l : List ModelBox => l[bIdx]?)
                (CanvasC1.tileStep_source c acc mid i hstep)
              simp only [List.getElem?_map] at h
              rw [hb, hn0mem] at h
              exact Option.some.inj h
            have hbpar_eq : b.source.parent = parent.source.id := by
              rw [hbSrc]; exact hn0par
            have holdid : old.source.id = parent.source.id := heq.trans hbpar_eq
            have hki : k = i := acc_index_eq_of_id_eq hnodup_acc hold hi_acc holdid
            exact hi_fresh (hki ▸ hk)
        · have hbnOut : mid[bIdx]? = acc[bIdx]? := hbOut bIdx (by
            intro q hq hq1
            exact hass (List.mem_map.mpr ⟨q, hq, hq1⟩))
          rw [hbnOut] at hb
          exact hdone k hk bIdx b hb hne old hold heq
      · -- `k = i`: freshly assigned children sit inside the parent tile.
        have hkeq : k = i := List.mem_singleton.mp hk
        subst hkeq
        rw [hi_mid] at hold
        have holdE : parent = old := Option.some.inj hold
        rw [holdE.symm] at heq ⊢
        by_cases hass : bIdx ∈
            ((sortedChildren acc parent.source.id).zip cells).map Prod.fst
        · obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hass
          cases q with
          | mk j cell =>
            have hqb : j = bIdx := hq1
            rw [hqb] at hq
            have hbmem : bIdx ∈ sortedChildren acc parent.source.id :=
              (List.of_mem_zip hq).1
            have hassignNodup : (((sortedChildren acc parent.source.id).zip
                cells).map Prod.fst).Nodup :=
              CanvasC1.zip_indices_nodup (sortedChildren acc parent.source.id) cells
                (CanvasC1.sortedChildren_index_nodup acc parent.source.id)
            obtain ⟨n0, hn0mem, _⟩ := CanvasC1.sortedChildren_index_source acc
              parent.source.id bIdx hbmem
            have hbrect : (mid[bIdx]?).map Node.rect =
                some (insetCell cell c.innerX c.innerY) := by
              rw [hout]
              exact CanvasC1.batch_getElem?_assigned acc
                ((sortedChildren acc parent.source.id).zip cells) c.innerX
                c.innerY hassignNodup (bIdx, cell) hq n0 hn0mem
            rw [hb] at hbrect
            simp only [Option.map_some] at hbrect
            have hbreq : b.rect = insetCell cell c.innerX c.innerY :=
              Option.some.inj hbrect
            rw [hbreq]
            have hvals : ∀ v ∈ (sortedChildren acc parent.source.id).map
                (fun j => (acc[j]?).map (·.value) |>.getD 0), 0 ≤ v :=
              squarify_values_nonnegative _
                (childArea parent.rect c.padX c.padY c.header c.innerX c.innerY)
                c.rho c.fuel cells capped hsq
            exact treemap_children_inside_parent
              ((sortedChildren acc parent.source.id).map
                (fun j => (acc[j]?).map (·.value) |>.getD 0))
              parent.rect c.padX c.padY c.header c.innerX c.innerY c.rho c.fuel
              cells capped hvals
              (hordered_acc parent (List.mem_of_getElem? hi_acc)) hsq
              _ (List.mem_map.mpr ⟨cell, (List.of_mem_zip hq).2, rfl⟩)
        · have hbFresh : ∀ q ∈ (sortedChildren acc parent.source.id).zip cells,
              q.1 ≠ bIdx := by
            intro q hq hq1
            exact hass (List.mem_map.mpr ⟨q, hq, hq1⟩)
          have hbnOut : mid[bIdx]? = acc[bIdx]? := hbOut bIdx hbFresh
          rw [hbnOut] at hb
          have hpar : b.source.parent = parent.source.id := heq.symm
          have hmemIdx : bIdx ∈ sortedChildren acc parent.source.id :=
            CanvasC1.sortedChildren_mem_of_lookup acc parent.source.id bIdx b hb hpar
          exfalso
          obtain ⟨pos, hposlt, hpose⟩ := List.mem_iff_getElem.mp hmemIdx
          have hposclt : pos < cells.length := by omega
          have hzipmem : (bIdx, cells[pos]'hposclt) ∈
              (sortedChildren acc parent.source.id).zip cells := by
            rw [List.mem_iff_getElem?]
            refine ⟨pos, ?_⟩
            rw [List.getElem?_zip_eq_some]
            exact ⟨List.getElem?_eq_some_iff.mpr ⟨hposlt, hpose⟩,
              List.getElem?_eq_some_iff.mpr ⟨hposclt, rfl⟩⟩
          exact hbFresh _ hzipmem rfl

/-- The tile fold preserves `ProcessedContained` through the whole
    dependency order. -/
theorem fold_processedContained {m : Model} (hwf : WellFormed m)
    (nodes0 : List Node) (hsources0 : nodes0.map Node.source = m.boxes)
    (hid0 : ∀ n ∈ nodes0, n.source.id ≠ "")
    (hself0 : ∀ n ∈ nodes0, n.source.parent ≠ n.source.id)
    {c : Consts} {band : Int} (out : List Node)
    (hnodup0 : (nodes0.map (fun n => n.source.id)).Nodup)
    (hseed_inv : ∀ n ∈ nodes0, n.rect.Ordered ∧
      Rect.Contained (tileRect (CanvasC1.canvasTile c band)) (tileRect n.rect))
    (h : tileNodes c nodes0 = .ok out) :
    ProcessedContained out (dependencyOrder nodes0) := by
  rw [CanvasC1.tileNodes_eq_foldlM] at h
  have gen : ∀ (l : List Nat) (acc : List Node) (done : List Nat) (out : List Node),
      done ++ l = dependencyOrder nodes0 →
      acc.map Node.source = nodes0.map Node.source →
      (acc.map (fun n => n.source.id)).Nodup →
      (∀ n ∈ acc, n.rect.Ordered ∧
        Rect.Contained (tileRect (CanvasC1.canvasTile c band)) (tileRect n.rect)) →
      ProcessedContained acc done →
      l.foldlM (CanvasC1.tileStep c) acc = .ok out →
      ProcessedContained out (done ++ l) := by
    intro l
    induction l with
    | nil =>
      intro acc done out hord _ _ _ hdone hfold
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hfold
      subst hfold
      simpa using hdone
    | cons j js ih =>
      intro acc done out hord hsrc hnod hinv hdone hfold
      simp only [List.foldlM] at hfold
      obtain ⟨mid, hmid, hrest⟩ := CanvasC1.except_bind_ok hfold
      have htsrc : mid.map Node.source = nodes0.map Node.source := by
        rw [CanvasC1.tileStep_source c acc mid j hmid, hsrc]
      have htnod : (mid.map (fun n => n.source.id)).Nodup := by
        have hA : mid.map (fun n => n.source.id) =
            List.map (fun x => x.id) (List.map Node.source mid) := by
          rw [List.map_map]
          rfl
        have hB : nodes0.map (fun n => n.source.id) =
            List.map (fun x => x.id) (List.map Node.source nodes0) := by
          rw [List.map_map]
          rfl
        rw [hA, congrArg (fun (l : List ModelBox) => l.map (·.id)) htsrc, ← hB]
        exact hnodup0
      have hstep := tileStep_contained hwf nodes0 hsources0 hid0 hself0 hsrc hnod
        (fun n hn => (hinv n hn).1) hdone hord hmid
      have hinvmid := CanvasC1.tileStep_invariant c band acc j mid hinv hmid
      have hres := ih mid (done ++ [j]) out
        (by rw [List.append_assoc]; exact hord)
        htsrc htnod hinvmid hstep hrest
      simpa only [List.append_assoc, List.singleton_append] using hres
  have h0 := gen (dependencyOrder nodes0) nodes0 [] out rfl rfl hnodup0 hseed_inv
    (fun k hk => absurd hk List.not_mem_nil) h
  simpa using h0

/-- Clause 3 for the treemap adapter: every admitted successful layout places
    each non-root dump box inside the dump box carrying its parent id. -/
theorem treemap_c3 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (h : Kinds.Treemap.layout m = .ok result) :
    Validator.C3 result.scene.layoutDump := by
  intro b hbmem hbpar p hplookup
  obtain ⟨final, hfinal, hboxes, _, _⟩ := layout_execution m result.scene
    (Kinds.Treemap.layout_adapter_success m result h)
  let seed : List Node := (assignSeries (aggregate (initialNodes m))).map fun n =>
      if n.source.id == "root" then
        { n with rect := ⟨0,
            if (labelText m "title").isEmpty then 0 else (constants m).titleBand,
            (constants m).width,
            (if (labelText m "title").isEmpty then 0 else (constants m).titleBand) +
              (constants m).height⟩ }
      else n
  have hbmem' : b ∈ result.scene.boxes := hbmem
  have hpm : p ∈ result.scene.boxes := List.mem_of_find?_eq_some hplookup
  rw [hboxes] at hbmem' hpm
  obtain ⟨n, hnmem, rfl⟩ := List.mem_map.mp hbmem'
  -- Seed sources and id hygiene.
  have hseedsrc : seed.map Node.source = m.boxes :=
    CanvasC1.seeded_source m
  have hnonempty : ∀ t ∈ seed, t.source.id ≠ "" := by
    intro t ht
    exact Kinds.Treemap.layout_box_ids_nonempty m result h t.source
      (by rw [← hseedsrc]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
  have hnodup_seed : (seed.map (fun t => t.source.id)).Nodup := by
    have h1 : seed.map (fun t => t.source.id) = m.boxes.map (fun b => b.id) := by
      have h2 := congrArg (fun l : List ModelBox => l.map (fun b => b.id)) hseedsrc
      rw [List.map_map] at h2
      exact h2
    rw [h1]
    exact Model.boxIds_nodup hwf
  have hself0 : ∀ t ∈ seed, t.source.parent ≠ t.source.id :=
    nodes_parent_ne_id hwf seed hseedsrc hnodup_seed hnonempty
  -- Seed order/canvas invariant.
  have hband : 0 ≤ CanvasC1.bandOf m := CanvasC1.bandOf_nonneg m
  have hw := Kinds.Treemap.layout_width_nonnegative m result h
  have hh := Kinds.Treemap.layout_height_nonnegative m result h
  have hseedinv : ∀ t ∈ seed, t.rect.Ordered ∧
      Rect.Contained
        (tileRect (CanvasC1.canvasTile (constants m) (CanvasC1.bandOf m)))
        (tileRect t.rect) :=
    CanvasC1.seeded_invariant m hw hh hband
  have hinv := fold_processedContained hwf seed hseedsrc hnonempty hself0 final
    hnodup_seed hseedinv hfinal
  -- Indices of the child and parent nodes in the final node list.
  obtain ⟨nIdx, hnIdx⟩ := List.mem_iff_getElem?.mp hnmem
  have hlen : final.length = seed.length := by
    have h1 := congrArg List.length
      (CanvasC1.tileNodes_source (constants m) seed final hfinal)
    simpa only [List.length_map] using h1
  have hidxord : ∀ t ∈ final, ∀ j : Nat, final[j]? = some t →
      j ∈ dependencyOrder seed := by
    intro t _ j hj
    obtain ⟨jlt, _⟩ := List.getElem?_eq_some_iff.mp hj
    apply (CanvasC1.dependencyOrder_perm_indices seed).mem_iff.mpr
    rw [List.zipIdx_map_snd]
    rw [List.mem_range'_1]
    exact ⟨Nat.zero_le j, by omega⟩
  -- The parent dump box is the image of the parent node.
  obtain ⟨pn, hpnmem, rfl⟩ := List.mem_map.mp hpm
  have hpnid : pn.source.id = n.source.parent := by
    simpa using List.find?_some hplookup
  obtain ⟨pIdx, hpIdx⟩ := List.mem_iff_getElem?.mp hpnmem
  exact hinv pIdx (hidxord pn hpnmem pIdx hpIdx) nIdx n hnIdx hbpar pn hpIdx hpnid

end C3

end Elegant.Treemap.Containment