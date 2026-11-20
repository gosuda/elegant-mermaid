import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem SizingRelated.getElem?_right {α β : Type} {r : α → β → Prop}
    {as : List α} {bs : List β} (h : SizingRelated r as bs)
    {i : Nat} {b : β} (hb : bs[i]? = some b) :
    ∃ a, as[i]? = some a ∧ r a b := by
  induction h generalizing i with
  | nil => simp at hb
  | @cons a head rest tail hab hrest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst b
      exact ⟨a, rfl, hab⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hb ⊢
      exact ih hb

theorem sizedNodes_index_text_fit {profile : Profile} {kind : String} {P : Params}
    {lines : List (List Measure.Line)} {ns : List Node}
    (hp : checkedParams profile kind = .ok P)
    (hn : sizedNodes P lines = .ok ns)
    {i : Nat} {n : Node} (hget : ns[i]? = some n) :
    ∃ ls, lines[i]? = some ls ∧ n.decl = i ∧
      ls.foldl (fun w line => max w line.width) 0 ≤ n.w ∧
      (ls.length : Int) * P.lineH ≤ n.h := by
  obtain ⟨q, hq, hfit⟩ := (checkedParams_sizedNodes_text_fit hp hn).getElem?_right hget
  cases hl : lines[i]? with
  | none => simp only [List.getElem?_zipIdx, hl, Option.map_none] at hq; cases hq
  | some ls =>
    simp only [List.getElem?_zipIdx, hl, Option.map_some, Nat.zero_add,
      Option.some.injEq] at hq
    subst q
    exact ⟨ls, rfl, hfit⟩

theorem prepare_node_record (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) {i : Nat} {node : Node}
    (hn : g.nodes[i]? = some node) {box : ModelBox}
    (hb : boxes[i]? = some box) (hrole : box.role = .node) :
    (Compound.prepare boxes pad titles g).nodes[i]? =
      some { node with clusterPath := Compound.path boxes box } := by
  have hi : i < g.nodes.length := (List.getElem?_eq_some_iff.mp hn).1
  rw [Compound.prepare_nodes]
  unfold Compound.markNodes
  dsimp only
  rw [List.getElem?_append_left (by simpa only [List.length_map, List.length_zipIdx] using hi)]
  simp only [List.getElem?_map, List.getElem?_zipIdx, hn, Option.map_some,
    Nat.zero_add, hb, hrole]
  rfl

theorem measuredGraph_node_text_fit
    {profile : Profile} {kind : String} {P : Params}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)} {g : Graph}
    (hp : checkedParams profile kind = .ok P)
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box) (hrole : box.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false) :
    ∃ node, g.nodes[i]? = some node ∧ node.decl = i ∧
      (match o.direction with
        | .LR | .RL => (ls.length : Int) * P.lineH
        | .TB | .BT => ls.foldl (fun w line => max w line.width) 0) ≤ node.w ∧
      (match o.direction with
        | .LR | .RL => ls.foldl (fun w line => max w line.width) 0
        | .TB | .BT => (ls.length : Int) * P.lineH) ≤ node.h := by
  have hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hgraph := Except.ok.inj hg
  subst g
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, hsized, hbefore⟩ := hinit i (ls, i)
    (by simp only [List.getElem?_zipIdx, hline, Option.map_some, Nat.zero_add])
  obtain ⟨_, _, hx, hy, hb⟩ := checkedParams_sizing_nonneg hp
  have hfit := sizedNode_text_fit hx hy hb hsized
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ := hprocessed i (orientNode o.direction before, i)
    (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
      Option.map_some, Nat.zero_add])
  have hprepared := prepare_node_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) P.clusterPad
      (lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * P.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      { nodes := nodes, edges := edges, slot := P.slot }
      hafter (by simp only [List.getElem?_map, hbox, Option.map_some,
        hfixed, Bool.false_eq_true, ↓reduceIte]) hrole
  refine ⟨_, hprepared, ?_, ?_, ?_⟩
  all_goals
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at hstep
    simp [hfind, hbox, hrole] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · have he := Except.ok.inj hstep
        subst after
        have hh := Int.le_max_left (orientNode o.direction before).h
          (Loops.requiredHeight P.slot (loopSizes edges labels i P.slot))
        cases o.direction <;> simp only [orientNode] at * <;> omega

theorem normalize_node_record {g : Graph} {ranks : List Int} {p : Proper}
    (h : NormalizeImpl.normalize g ranks = .ok p)
    {i : Nat} {n : Node} (hn : g.nodes[i]? = some n) :
    p.nodes[i]? = some ⟨n, false, none, false⟩ := by
  have edge_preserves {slot : Int} {q q' : Proper} {e : Edge} {idx : Nat}
      (he : NormalizeImpl.normalizeEdge slot q e idx = .ok q')
      {node : ProperNode} (hq : q.nodes[i]? = some node) :
      q'.nodes[i]? = some node := by
    unfold NormalizeImpl.normalizeEdge at he
    split at he
    · cases he
      exact hq
    · split at he
      · cases he
      · split at he
        · cases he
        · cases he
          exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hq).1).trans hq
  have loop_preserves {slot : Int} (entries : List (Edge × Nat))
      (q q' : Proper) (he : NormalizeImpl.normalizeLoop slot entries q = .ok q')
      {node : ProperNode} (hq : q.nodes[i]? = some node) :
      q'.nodes[i]? = some node := by
    induction entries generalizing q with
    | nil =>
      cases he
      exact hq
    | cons entry entries ih =>
      simp only [NormalizeImpl.normalizeLoop] at he
      split at he
      · cases he
      · rename_i next hnext
        exact ih next he (edge_preserves hnext hq)
  unfold NormalizeImpl.normalize at h
  split at h
  · cases h
  · split at h
    · exact loop_preserves _ _ _ h (by simp only [List.getElem?_map, hn, Option.map_some])
    · cases h

theorem addLabelNodes_untouched_node {g : Graph} {p q : Proper}
    {labels : List EdgeLabelSize} {i : Nat} {node : ProperNode}
    (h : Labels.addLabelNodes g p labels = .ok q)
    (hn : p.nodes[i]? = some node) (he : node.edge = none) :
    q.nodes[i]? = some node := by
  induction labels generalizing p with
  | nil =>
    have heq : p = q := Except.ok.inj h
    subst q
    exact hn
  | cons label labels ih =>
    simp only [Labels.addLabelNodes] at h
    obtain ⟨next, hnext, h⟩ := bind_ok h
    have hother : node.edge ≠ some label.edge := by simp [he]
    exact ih h (addLabelNode_preserves_other_edge hn hother hnext)

theorem componentRun_original_node_dims
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node)
    (hb : node.border = 0) :
    ∃ out, run.proper.nodes[i]? = some out ∧ out.edge = none ∧
      out.node.border = 0 ∧ node.w ≤ out.node.w ∧ out.node.h = node.h := by
  obtain ⟨_, _, _, _, hnormalize, hlabels, hcoordinate, _⟩ := componentRun_spec h
  have hp := normalize_node_record hnormalize hn
  have hl := addLabelNodes_untouched_node hlabels hp rfl
  exact componentRun_coordinateGraph_plain_node_dims h hcoordinate hl hb

theorem indexed_rect_minimum_dimensions_preserved
    (minimum : Nat → Size) (dx dy : Int) (entries : List (Nat × Rect))
    (initial : Array Rect)
    (hinit : ∀ i rect, initial[i]? = some rect →
      (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h)
    (hwrites : ∀ entry ∈ entries,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h) :
    ∀ i rect,
      (entries.foldl (fun out entry =>
        if entry.1 < out.size then
          out.set! entry.1 (shiftRect dx dy entry.2) else out) initial)[i]? = some rect →
      (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h := by
  induction entries generalizing initial with
  | nil => exact hinit
  | cons entry entries ih =>
    rw [List.foldl_cons]
    apply ih
    · intro i rect hget
      split at hget
      · rename_i hin
        by_cases heq : entry.1 = i
        · subst i
          rw [getElem?_set!_self hin] at hget
          have hr := Option.some.inj hget
          rw [← hr]
          exact hwrites entry List.mem_cons_self
        · rw [getElem?_set!_ne heq] at hget
          exact hinit i rect hget
      · exact hinit i rect hget
    · intro written hmem
      exact hwrites written (List.mem_cons_of_mem entry hmem)

theorem packAcc_rect_minimum_dimensions
    {P : Params} {o : Options} {acc out : Acc}
    (minimum : Nat → Size)
    (hpack : packAcc P o acc = .ok out)
    (hinit : ∀ i rect, acc.rects[i]? = some rect →
      (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h)
    (hparts : ∀ part ∈ acc.parts, ∀ entry ∈ part.1.zip part.2.rects,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h) :
    ∀ i rect, out.rects[i]? = some rect →
      (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h := by
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  have hout := Except.ok.inj hpack
  subst out
  have preserve : ∀ (pairs : List ((List Nat × Part) × Rect)) (initial : Acc),
      (∀ pair ∈ pairs, pair.1 ∈ acc.parts) →
      (∀ i rect, initial.rects[i]? = some rect →
        (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h) →
      ∀ i rect,
        (pairs.foldl (fun state pair =>
          { state with
            rects := (pair.1.1.zip pair.1.2.rects).foldl
              (fun a entry => if entry.1 < a.size then
                a.set! entry.1 (shiftRect pair.2.x pair.2.y entry.2) else a) state.rects
            routes := pair.1.2.routes.foldl
              (fun a entry => a.set! entry.1
                (entry.2.map (shiftPoint pair.2.x pair.2.y))) state.routes
            labels := pair.1.2.labels.foldl
              (fun a entry => a.set! entry.1
                (shiftRect pair.2.x pair.2.y entry.2)) state.labels
            titles := state.titles ++ pair.1.2.titles.map
              (fun entry => (pair.1.1.getD entry.1 0,
                shiftRect pair.2.x pair.2.y entry.2)) }) initial).rects[i]? = some rect →
        (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h := by
    intro pairs
    induction pairs with
    | nil =>
      intro initial _ hi
      exact hi
    | cons pair pairs ih =>
      intro initial hp hi
      rw [List.foldl_cons]
      apply ih
      · intro other ho
        exact hp other (List.mem_cons_of_mem pair ho)
      · exact indexed_rect_minimum_dimensions_preserved minimum pair.2.x pair.2.y
          (pair.1.1.zip pair.1.2.rects) initial.rects hi
          (hparts pair.1 (hp pair List.mem_cons_self))
  apply preserve
  · intro pair hp
    exact (List.of_mem_zip hp).1
  · exact hinit

theorem caption_index_of_unique_ids {inp : Input}
    (hids : (inp.boxes.map (·.id)).Nodup)
    {i : Nat} {box : ModelBox} (hbox : inp.boxes[i]? = some box) :
    inp.boxes.findIdx? (fun candidate => candidate.id == box.id) = some i := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hbox
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨hi, ?_, ?_⟩
  · simp only [he, beq_self_eq_true]
  · intro j hj hsame
    have hji : j = i := by
      apply hids.eq_of_getElem_eq
        (by simpa only [List.length_map] using Nat.lt_trans hj hi)
        (by simpa only [List.length_map] using hi)
      simpa only [List.getElem_map, he] using (beq_iff_eq.mp hsame)
    omega

theorem FrameOrigin.title_fit {o : Options} {id : String} {size : Size}
    (origin : FrameOrigin o id size) :
    origin.titleLines.foldl (fun width line => max width line.width) 0 +
        2 * origin.params.clusterPad ≤ size.w ∧
      (max 1 origin.titleLines.length : Int) * origin.params.lineH +
        2 * origin.params.clusterPad ≤ size.h := by
  have fit := childFrameSize_title_fit origin.group.direction origin.params.clusterPad
    (origin.titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 origin.titleLines.length : Int) * origin.params.lineH)
    ⟨_, _⟩ origin.content_nonneg.1 origin.content_nonneg.2
  have hw := congrArg Size.w origin.size_eq
  have hh := congrArg Size.h origin.size_eq
  exact ⟨hw.symm ▸ fit.1, hh.symm ▸ fit.2⟩

theorem measuredGraph_fixed_node_dims
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry) :
    ∃ node, g.nodes[i]? = some node ∧ node.decl = i ∧ node.border = 0 ∧
      (match o.direction with
        | .LR | .RL => entry.2.h
        | .TB | .BT => entry.2.w) ≤ node.w ∧
      (match o.direction with
        | .LR | .RL => entry.2.w
        | .TB | .BT => entry.2.h) ≤ node.h := by
  have hany : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true :=
    List.any_eq_true.mpr
      ⟨entry, List.mem_of_find?_eq_some hfixed, by simpa using List.find?_some hfixed⟩
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hgraph := Except.ok.inj hg
  subst g
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, hsized, hbefore⟩ := hinit i (ls, i)
    (by simp only [List.getElem?_zipIdx, hline, Option.map_some, Nat.zero_add])
  have hmetadata : before.decl = i ∧ before.border = 0 := by
    unfold sizedNode at hsized
    obtain ⟨size, _, he⟩ := bind_ok hsized
    cases Except.ok.inj he
    exact ⟨rfl, rfl⟩
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ := hprocessed i (orientNode o.direction before, i)
    (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
      Option.map_some, Nat.zero_add])
  have hprepared := prepare_node_record (box := { box with role := .node })
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) P.clusterPad
      (lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * P.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      { nodes := nodes, edges := edges, slot := P.slot }
      hafter (by simp only [List.getElem?_map, hbox, Option.map_some,
        hany, ↓reduceIte]) rfl
  refine ⟨_, hprepared, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at hstep
    simp [hbox, hfixed, hany] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · have he := Except.ok.inj hstep
        subst after
        cases o.direction <;> simp only [orientNode] at * <;> omega

theorem componentRun_original_frame_minimum_dims
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node)
    (hb : node.border = 0) :
    node.w ≤ (frameRect P cg run i).w ∧ node.h ≤ (frameRect P cg run i).h := by
  obtain ⟨out, hout, _, _, hw, hh⟩ := componentRun_original_node_dims h hn hb
  have hget : cg.nodes.getD i default = node := by
    simp only [List.getD_eq_getElem?_getD, hn, Option.getD_some]
  have hplain : (cg.nodes.getD i default).border ≠ -2 := by
    rw [hget, hb]
    decide
  have hdims := frameRect_plain_dims P cg run i out hplain hout
  refine ⟨hdims.1.symm ▸ hw, ?_⟩
  rw [hdims.2, hh]
  exact Int.le_refl _

theorem SceneExecution.component_rect_minimum_dims
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = 0)
    {rect : Rect} (hrect : part.2.rects[i]? = some rect) :
    node.w ≤ rect.w ∧ node.h ≤ rect.h := by
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  have hnodes : (componentCandidate execution.graph part.1 index).nodes =
      part.1.map (fun key => execution.graph.nodes.getD key default) := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hlocal : (componentCandidate execution.graph part.1 index).nodes[i]? =
      some node := by
    rw [hnodes]
    simp only [List.getElem?_map, hkey, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hminimum := componentRun_original_frame_minimum_dims hrun hlocal hborder
  have hdims :
      part.2.rects.map (fun rect => (rect.w, rect.h)) =
        (List.range (componentCandidate execution.graph part.1 index).nodes.length).map
          (fun j =>
            ((frameRect execution.params
              (componentCandidate execution.graph part.1 index) run j).w,
             (frameRect execution.params
              (componentCandidate execution.graph part.1 index) run j).h)) := by
    rw [hplace]
    exact Layered.placeComponent_rect_dimensions execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
  have hi : i < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hlocal).1
  have hindex := congrArg (fun values : List (Int × Int) => values[i]?) hdims
  simp only [List.getElem?_map, hrect, Option.map_some,
    List.getElem?_range hi] at hindex
  have heq := Option.some.inj hindex
  exact ⟨by rw [Prod.mk.inj heq |>.1]; exact hminimum.1,
    by rw [Prod.mk.inj heq |>.2]; exact hminimum.2⟩

theorem indexed_rect_minimum_dimensions_pending
    (minimum : Nat → Size) (dx dy : Int) (entries : List (Nat × Rect))
    (initial : Array Rect) (pending : Nat → Prop)
    (hinit : ∀ i rect, initial[i]? = some rect →
      ((minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h) ∨
        (∃ entry ∈ entries, entry.1 = i) ∨ pending i)
    (hwrites : ∀ entry ∈ entries,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h) :
    ∀ i rect,
      (entries.foldl (fun out entry =>
        if entry.1 < out.size then
          out.set! entry.1 (shiftRect dx dy entry.2) else out) initial)[i]? = some rect →
      ((minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h) ∨ pending i := by
  induction entries generalizing initial with
  | nil =>
    intro i rect hget
    rcases hinit i rect hget with hfit | ⟨entry, hmem, _⟩ | hrem
    · exact Or.inl hfit
    · simp at hmem
    · exact Or.inr hrem
  | cons entry entries ih =>
    rw [List.foldl_cons]
    apply ih
    · intro i rect hget
      by_cases heq : entry.1 = i
      · subst i
        by_cases hin : entry.1 < initial.size
        · rw [ite_eq_left hin, getElem?_set!_self hin] at hget
          have hr := Option.some.inj hget
          rw [← hr]
          exact Or.inl (hwrites entry List.mem_cons_self)
        · rw [ite_eq_right hin] at hget
          rw [Array.getElem?_eq_none (Nat.not_lt.mp hin)] at hget
          cases hget
      · split at hget <;> try rw [getElem?_set!_ne heq] at hget
        all_goals
          rcases hinit i rect hget with hfit | ⟨written, hmem, hkey⟩ | hrem
          · exact Or.inl hfit
          · rcases List.mem_cons.mp hmem with rfl | htail
            · exact False.elim (heq hkey)
            · exact Or.inr (Or.inl ⟨written, htail, hkey⟩)
          · exact Or.inr (Or.inr hrem)
    · intro written hmem
      exact hwrites written (List.mem_cons_of_mem entry hmem)

theorem packFold_rect_minimum_dimensions_pending
    (minimum : Nat → Size) (pairs : List ((List Nat × Part) × Rect))
    (initial : Acc)
    (hinit : ∀ i rect, initial.rects[i]? = some rect →
      ((minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h) ∨
        ∃ pair ∈ pairs, ∃ entry ∈ pair.1.1.zip pair.1.2.rects, entry.1 = i)
    (hwrites : ∀ pair ∈ pairs, ∀ entry ∈ pair.1.1.zip pair.1.2.rects,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h) :
    ∀ i rect, (pairs.foldl packStep initial).rects[i]? = some rect →
      (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h := by
  induction pairs generalizing initial with
  | nil =>
    intro i rect hget
    rcases hinit i rect hget with hfit | ⟨pair, hmem, _⟩
    · exact hfit
    · simp at hmem
  | cons pair pairs ih =>
    rw [List.foldl_cons]
    apply ih
    · change ∀ i rect,
        ((pair.1.1.zip pair.1.2.rects).foldl
          (fun out entry => if entry.1 < out.size then
            out.set! entry.1 (shiftRect pair.2.x pair.2.y entry.2) else out)
          initial.rects)[i]? = some rect → _
      apply indexed_rect_minimum_dimensions_pending minimum pair.2.x pair.2.y
        (pair.1.1.zip pair.1.2.rects) initial.rects
        (fun i => ∃ next ∈ pairs, ∃ entry ∈ next.1.1.zip next.1.2.rects, entry.1 = i)
      · intro i rect hget
        rcases hinit i rect hget with hfit | ⟨next, hnext, entry, hentry, hkey⟩
        · exact Or.inl hfit
        · rcases List.mem_cons.mp hnext with rfl | htail
          · exact Or.inr (Or.inl ⟨entry, hentry, hkey⟩)
          · exact Or.inr (Or.inr ⟨next, htail, entry, hentry, hkey⟩)
      · exact hwrites pair List.mem_cons_self
    · intro next hnext
      exact hwrites next (List.mem_cons_of_mem pair hnext)

theorem packAcc_rect_minimum_dimensions_of_coverage
    {P : Params} {o : Options} {acc out : Acc}
    (minimum : Nat → Size) (hpack : packAcc P o acc = .ok out)
    (hinit : ∀ i rect, acc.rects[i]? = some rect →
      ((minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h) ∨
        ∃ part ∈ acc.parts, ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i)
    (hparts : ∀ part ∈ acc.parts, ∀ entry ∈ part.1.zip part.2.rects,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h) :
    ∀ i rect, out.rects[i]? = some rect →
      (minimum i).w ≤ rect.w ∧ (minimum i).h ≤ rect.h := by
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, hpack⟩ := bind_ok hpack
  have hout := Except.ok.inj hpack
  subst out
  change ∀ i rect,
    ((acc.parts.zip packed.boxes).foldl packStep
      { acc with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects[i]? =
        some rect → _
  apply packFold_rect_minimum_dimensions_pending minimum
  · intro i rect hget
    rcases hinit i rect hget with hfit | ⟨part, hpart, entry, hentry, hkey⟩
    · exact Or.inl hfit
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem hpart
      have hkl : k < acc.parts.length := (List.getElem?_eq_some_iff.mp hk).1
      have hcount := Pack.pack_count hpacked
      have hbk : k < packed.boxes.length := by
        simp only [List.length_map] at hcount
        omega
      have hbox : packed.boxes[k]? = some packed.boxes[k] :=
        List.getElem?_eq_some_iff.mpr ⟨hbk, rfl⟩
      exact Or.inr ⟨(part, packed.boxes[k]), zip_mem_of_getElem? hk hbox,
        entry, hentry, hkey⟩
  · intro pair hpair
    exact hparts pair.1 (List.of_mem_zip hpair).1

theorem SceneExecution.packed_rect_minimum_dims_of_coverage
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hcoverage : ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      ∃ part ∈ execution.componentsAcc.parts,
        ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i)
    {key : Nat} {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = 0)
    {rect : Rect} (hrect : execution.packedAcc.rects[key]? = some rect) :
    node.w ≤ rect.w ∧ node.h ≤ rect.h := by
  let minimum : Nat → Size := fun i =>
    match execution.graph.nodes[i]? with
    | some n => if n.border = 0 then ⟨n.w, n.h⟩ else ⟨0, 0⟩
    | none => ⟨0, 0⟩
  have hparts : ∀ part ∈ execution.componentsAcc.parts,
      ∀ entry ∈ part.1.zip part.2.rects,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h := by
    intro part hpart entry hentry
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hentry
    simp only [List.length_zip] at hi
    have hil : i < part.1.length := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hir : i < part.2.rects.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hpair : (part.1[i], part.2.rects[i]) = entry := by
      simpa only [List.getElem_zip] using heq
    have hkey : part.1[i]? = some entry.1 := by
      rw [List.getElem?_eq_getElem hil, ← hpair]
    have hget : part.2.rects[i]? = some entry.2 := by
      rw [List.getElem?_eq_getElem hir, ← hpair]
    have hn : 0 ≤ entry.2.w ∧ 0 ≤ entry.2.h := by
      have hb := execution.components_parts_bounded part hpart
      have hm := (List.of_mem_zip hentry).2
      exact ⟨(hb.2.2.1 entry.2 hm).2.2.2.2.1,
        (hb.2.2.1 entry.2 hm).2.2.2.2.2⟩
    dsimp only [minimum]
    cases hlookup : execution.graph.nodes[entry.1]? with
    | none => exact hn
    | some n =>
      by_cases hb : n.border = 0
      · simp only [hb, ↓reduceIte]
        exact execution.component_rect_minimum_dims hpart hkey hlookup hb hget
      · simpa only [hb, ↓reduceIte] using hn
  have hfit := packAcc_rect_minimum_dimensions_of_coverage minimum execution.packed_eq
    (fun i r hr => Or.inr (hcoverage i r hr)) hparts key rect hrect
  simpa only [minimum, hnode, hborder, ↓reduceIte] using hfit

theorem SceneExecution.box_index_origin
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {index : Nat} {box : Box}
    (hbox : res.scene.boxes[index]? = some box) :
    ∃ source, inp.boxes[index]? = some source ∧
      box = Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD index default))) source.parent source.exclusive := by
  rw [execution.boxes_eq_map] at hbox
  cases hs : inp.boxes[index]? with
  | none => simp [hs] at hbox
  | some source =>
    refine ⟨source, rfl, ?_⟩
    simpa [hs] using hbox.symm

end Elegant.Layered.PipelineImpl
