import Elegant.Layered.RegionNotesContractedRootGraph

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl.ContractedC8a

open RegionImpl

private def eraseParent (b : Box) : Box := { b with parent := "" }
private def eraseParents (s : Scene) : Scene := { s with boxes := s.boxes.map eraseParent }

private theorem erase_box_find (xs : List Box) (id : String) :
    (xs.map eraseParent).find? (fun b => b.id == id) =
      (xs.find? (fun b => b.id == id)).map eraseParent := by
  rw [List.find?_map] <;> rfl

private theorem erase_find_rects (xs : List Box) (a b : String) (f : Rect → Rect → Int) (n : Int) :
    (match (xs.map eraseParent).find? (fun x => x.id == a),
        (xs.map eraseParent).find? (fun x => x.id == b) with
      | some x, some y => f x.rect y.rect
      | _, _ => n) =
    (match xs.find? (fun x => x.id == a), xs.find? (fun x => x.id == b) with
      | some x, some y => f x.rect y.rect
      | _, _ => n) := by
  rw [erase_box_find, erase_box_find]
  cases xs.find? (fun x => x.id == a) <;> cases xs.find? (fun x => x.id == b) <;> rfl

private theorem erase_cost (s : Scene) : softCost (eraseParents s) = softCost s := by
  let nodes (boxes : List Box) := boxes.filter (fun b => b.role == "node")
  let extent (n : Int) (b : Box) := n + Int.fdiv (b.rect.w + b.rect.h) 2
  let step (n : Int) (a b : Rect) : Int :=
    let d := match s.options.direction with
      | .TB => 2 * b.y + b.h - (2 * a.y + a.h)
      | .BT => 2 * a.y + a.h - (2 * b.y + b.h)
      | .LR => 2 * b.x + b.w - (2 * a.x + a.w)
      | .RL => 2 * a.x + a.w - (2 * b.x + b.w)
    n + if d < 0 then 1 else 0
  let against (boxes : List Box) (n : Int) (r : Route) :=
    match boxes.find? (fun b => b.id == r.fromId), boxes.find? (fun b => b.id == r.toId) with
    | some a, some b => step n a.rect b.rect
    | _, _ => n
  have hrects : (s.boxes.map eraseParent).map Box.rect = s.boxes.map Box.rect := by
    rw [List.map_map] <;> rfl
  have hnodes : nodes (s.boxes.map eraseParent) = (nodes s.boxes).map eraseParent := by
    unfold nodes
    rw [List.filter_map] <;> rfl
  have hcount : (nodes (s.boxes.map eraseParent)).length = (nodes s.boxes).length := by
    rw [hnodes, List.length_map]
  have hsum : (nodes (s.boxes.map eraseParent)).foldl extent 0 =
      (nodes s.boxes).foldl extent 0 := by
    rw [hnodes, List.foldl_map] <;> rfl
  have hagainst : against (s.boxes.map eraseParent) = against s.boxes :=
    funext (fun n => funext (fun r => erase_find_rects s.boxes r.fromId r.toId (step n) n))
  dsimp only [nodes] at hcount
  dsimp only [nodes, extent] at hsum
  dsimp only [against, step] at hagainst
  change softCost { s with boxes := s.boxes.map eraseParent } = softCost s
  unfold softCost
  try dsimp only
  simp only [hrects, hcount, hsum]
  first
  | erw [hagainst] <;> rfl
  | simpa only [hagainst]

private def eraseCandidate {α : Type} (c : Portfolio.Candidate α) : Portfolio.Candidate α :=
  { c with scene := eraseParents c.scene }

private def eraseScored {α : Type} (c : Portfolio.Scored α) : Portfolio.Scored α :=
  ⟨eraseCandidate c.candidate, c.cost, (erase_cost c.candidate.scene).trans c.cost_eq⟩

private theorem score_error {α : Type} (c : Portfolio.Candidate α) {e : LayoutError}
    (h : softCost c.scene = .error e) : Portfolio.score c = .error e := by
  unfold Portfolio.score
  split
  · rename_i other he
    exact congrArg Except.error (Except.error.inj (he.symm.trans h))
  · rename_i cost hc
    cases h.symm.trans hc

private theorem score_ok {α : Type} (c : Portfolio.Candidate α) {cost : Int}
    (h : softCost c.scene = .ok cost) : Portfolio.score c = .ok ⟨c, cost, h⟩ := by
  unfold Portfolio.score
  split
  · rename_i e he
    cases he.symm.trans h
  · rename_i other ho
    have hc : other = cost := Except.ok.inj (ho.symm.trans h)
    subst other
    rfl

private theorem erase_score {α : Type} (c : Portfolio.Candidate α) :
    Portfolio.score (eraseCandidate c) = (Portfolio.score c).map eraseScored := by
  cases hc : softCost c.scene with
  | error e =>
    rw [score_error (eraseCandidate c) ((erase_cost c.scene).trans hc), score_error c hc] <;> rfl
  | ok cost =>
    rw [score_ok (eraseCandidate c) ((erase_cost c.scene).trans hc), score_ok c hc] <;> rfl

private theorem erase_consider {α : Type} (a b : Portfolio.Scored α) :
    Portfolio.consider (eraseScored a) (eraseScored b) =
      (Portfolio.consider a b).map eraseScored := by
  unfold Portfolio.consider
  cases h : Portfolio.improves a.cost b.cost with
  | error e => simp [eraseScored, h, Except.map]
  | ok better =>
    cases better <;> simp [eraseScored, eraseCandidate, h, Except.map]

private theorem erase_run {α : Type} (candidate : Nat → Except LayoutError (Portfolio.Candidate α))
    (fuel index : Nat) (inc : Portfolio.Scored α) :
    Portfolio.run (fun i => (candidate i).map eraseCandidate) fuel index (eraseScored inc) =
      (Portfolio.run candidate fuel index inc).map eraseScored := by
  induction fuel generalizing index inc with
  | zero => rfl
  | succ fuel ih =>
    simp only [Portfolio.run]
    cases htrial : candidate index with
    | error e => rfl
    | ok trial =>
      simp only [Except.map, erase_score]
      cases hscore : Portfolio.score trial with
      | error e => rfl
      | ok scored =>
        simp only [Except.map, erase_consider]
        cases hc : Portfolio.consider inc scored with
        | error e => rfl
        | ok next => exact ih (index + 1) next

private theorem map_bind_transport {α β : Type} (eraseIn : α → α) (eraseOut : β → β)
    {a b : Except LayoutError α} (h : a = b.map eraseIn)
    {f g : α → Except LayoutError β}
    (hbody : ∀ x, f (eraseIn x) = (g x).map eraseOut) :
    (a >>= f) = (b >>= g).map eraseOut := by
  rw [h]
  cases b with
  | error e => rfl
  | ok x => exact hbody x

private theorem erase_portfolio {α : Type}
    (candidate : Nat → Except LayoutError (Portfolio.Candidate α)) (count : Nat) :
    Portfolio.portfolio count (fun i => (candidate i).map eraseCandidate) =
      (Portfolio.portfolio count candidate).map eraseCandidate := by
  unfold Portfolio.portfolio
  generalize (if count = 0 then 3 else count) = effectiveCount
  by_cases hcap : 5 < effectiveCount
  · simp only [ite_eq_left hcap] <;> rfl
  · simp only [ite_eq_right hcap]
    cases candidate 0 with
    | error e => rfl
    | ok first =>
      have hfirst : (Except.ok first : Except LayoutError (Portfolio.Candidate α)).map
          eraseCandidate = .ok (eraseCandidate first) := rfl
      simp only [hfirst, erase_score first]
      cases Portfolio.score first with
      | error e => rfl
      | ok initial =>
        have hinitial : (Except.ok initial : Except LayoutError (Portfolio.Scored α)).map
            eraseScored = .ok (eraseScored initial) := rfl
        simp only [hinitial]
        rw [erase_run candidate (min effectiveCount 5 - 1) 1 initial]
        cases Portfolio.run candidate (min effectiveCount 5 - 1) 1 initial <;> rfl

private theorem erase_shift_boxes (dx dy : Int) (outer child : List Box) :
    (outer ++ child.map (fun (box : Box) => { box with rect := shiftRect dx dy box.rect })).map eraseParent =
      outer.map eraseParent ++ (child.map eraseParent).map
        (fun (box : Box) => { box with rect := shiftRect dx dy box.rect }) := by
  simp only [List.map_append, List.map_map] <;> rfl

private theorem erase_expandedCost (P : Params) (inp : Input) (o : Options) (a b : Scene)
    (hs : eraseParents a = eraseParents b) :
    (expandedComponentCost P (rootInput inp) o a).map eraseParents =
      (expandedComponentCost P inp o b).map eraseParents := by
  let appendChild (s child : Scene) (frame : Box) (direction : String)
      (lines : List Measure.Line) : Scene :=
    let titleWidth := lines.foldl (fun width line => max width line.width) 0
    let inset := childInset direction P.clusterPad titleWidth ((max 1 lines.length : Int) * P.lineH)
    let dx := frame.rect.x + inset.x - P.canvasMargin
    let dy := frame.rect.y + inset.y - P.canvasMargin
    { s with
      boxes := s.boxes ++ child.boxes.map (fun (box : Box) =>
        { box with rect := shiftRect dx dy box.rect })
      routes := s.routes ++ child.routes.map (fun (route : Route) =>
        { route with points := route.points.map (shiftPoint dx dy) })
      labels := s.labels ++ child.labels.map (fun (label : SceneLabel) =>
        { label with rect := shiftRect dx dy label.rect }) }
  have hshift (s child : Scene) (frame : Box) (direction : String) (lines : List Measure.Line) :
      eraseParents (appendChild s child frame direction lines) =
        appendChild (eraseParents s) (eraseParents child) (eraseParent frame) direction lines := by
    dsimp only [appendChild, eraseParents]
    rw [erase_shift_boxes] <;> rfl
  let sameCostStep (inp : Input) (s : Scene) (child : String × Scene) : Except LayoutError Scene := do
    match s.boxes.find? (fun (box : Box) => box.id == child.1) with
    | none => pure s
    | some frame =>
      let metric ← metricOf o.profile o.fontFamily
      let index := (inp.boxes.findIdx? (fun (box : ModelBox) => box.id == child.1)).getD 0
      let lines ← StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == Profile.cell then o.maxWidth else 0))
        (inp.texts.getD index child.1).toList
      let direction := ((inp.boxes[index]?).map ModelBox.direction).getD ""
      pure (appendChild s child.2 frame direction lines)
  have hindex (id : String) :
      (rootInput inp).boxes.findIdx? (fun b => b.id == id) =
        inp.boxes.findIdx? (fun b => b.id == id) := by
    simp only [rootInput, List.findIdx?_map] <;> rfl
  have hdirection (i : Nat) :
      ((rootInput inp).boxes[i]?).map ModelBox.direction =
        (inp.boxes[i]?).map ModelBox.direction := by
    simp only [rootInput, List.getElem?_map, Option.map_map] <;> rfl
  have hrootStep (s : Scene) (child : String × Scene) :
      sameCostStep (rootInput inp) s child = sameCostStep inp s child := by
    simp only [sameCostStep, hindex, hdirection] <;> rfl
  have hstep' (s : Scene) (child : String × Scene) :
      (sameCostStep inp s child).map eraseParents =
        sameCostStep inp (eraseParents s) (child.1, eraseParents child.2) := by
    have hfind : (eraseParents s).boxes.find? (fun box => box.id == child.1) =
        (s.boxes.find? (fun box => box.id == child.1)).map eraseParent :=
      erase_box_find s.boxes child.1
    simp only [sameCostStep, hfind]
    cases hf : s.boxes.find? (fun box => box.id == child.1) with
    | none => rfl
    | some frame =>
      cases hm : metricOf o.profile o.fontFamily with
      | error e => rfl
      | ok metric =>
        simp only [bind, Except.bind]
        cases StyledMeasure.wrap metric
          (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == Profile.cell then o.maxWidth else 0))
          (inp.texts.getD ((inp.boxes.findIdx? (fun (box : ModelBox) => box.id == child.1)).getD 0) child.1).toList with
        | error e => rfl
        | ok lines =>
          let index := (inp.boxes.findIdx? (fun (box : ModelBox) => box.id == child.1)).getD 0
          let direction := ((inp.boxes[index]?).map ModelBox.direction).getD ""
          exact congrArg Except.ok (hshift s child.2 frame direction lines)
  change (inp.fixedChildren.foldlM (sameCostStep (rootInput inp)) a).map eraseParents =
    (inp.fixedChildren.foldlM (sameCostStep inp) b).map eraseParents
  have hfun : sameCostStep (rootInput inp) = sameCostStep inp :=
    funext (fun s => funext (hrootStep s))
  rw [hfun]
  generalize inp.fixedChildren = children
  induction children generalizing a b with
  | nil => exact congrArg Except.ok hs
  | cons child rest ih =>
    simp only [List.foldlM_cons]
    have hnext : (sameCostStep inp a child).map eraseParents =
        (sameCostStep inp b child).map eraseParents := by rw [hstep', hstep', hs]
    cases ha : sameCostStep inp a child with
    | error err =>
      cases hb : sameCostStep inp b child with
      | error err' =>
        have he : err = err' := by simpa only [ha, hb, Except.map, Except.error.injEq] using hnext
        subst err'
        rfl
      | ok b' => simp [ha, hb, Except.map] at hnext
    | ok a' =>
      cases hb : sameCostStep inp b child with
      | error err => simp [ha, hb, Except.map] at hnext
      | ok b' =>
        apply ih a' b'
        simpa only [ha, hb, Except.map, Except.ok.injEq] using hnext

private theorem erase_componentScene (P : Params) (inp : Input) (o : Options) (cg : Graph)
    (run : Run) (labels : List MeasuredLabel) :
    (componentScene P (rootInput inp) o cg run labels (@placeComponentExact)).map eraseParents =
      (componentScene P inp o cg run labels (@placeComponentExact)).map eraseParents := by
  have hlabel (owner : String) : (rootInput inp).boxes.any (fun b => b.id == owner && b.exclusive) =
      inp.boxes.any (fun b => b.id == owner && b.exclusive) := by
    simp only [rootInput, List.any_map, Function.comp_def]
    rfl
  unfold componentScene
  cases hloops : componentLoops P cg run labels with
  | error e => rfl
  | ok loops =>
    simp only [bind, Except.bind]
    let part := placeComponentExact P cg run 0 labels loops
    let emit (x : Input) := cg.nodes.zipIdx.filterMap fun q =>
      match x.boxes[q.1.decl]? with
      | none => none
      | some b => if q.1.border == 2 then none else
        some (Box.mk b.id b.role.id (orientRect o.direction part.height (part.rects.getD q.2 default))
          b.parent b.exclusive)
    let rootBox (b : Box) : Box := { b with parent := rootParent (inp.boxes.map ModelBox.id) b.parent }
    have hEmit : emit (rootInput inp) = (emit inp).map rootBox := by
      simp only [emit, List.map_filterMap, rootInput, List.getElem?_map]
      congr 1
      funext q
      cases inp.boxes[q.1.decl]? with
      | none => rfl
      | some b =>
        by_cases hb : q.1.border == 2 <;> simp [hb] <;> rfl
    have hEqErase : (emit (rootInput inp)).map eraseParent = (emit inp).map eraseParent := by
      rw [hEmit, List.map_map] <;> rfl
    let title (metric : Measure.Metric) (boxes : List Box) (model : ModelLabel) :
        Except LayoutError (Option SceneLabel) := do
      match boxes.find? (fun box => box.id == model.owner && !box.exclusive) with
      | none => pure none
      | some frame =>
        let lines ← StyledMeasure.wrap metric
          (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == Profile.cell then o.maxWidth else 0))
          model.text.toList
        pure (some ({
          id := model.id, owner := model.owner, text := model.text
          rect := ownedTextRect P frame lines
          lines := lines.map fun line => String.ofList line.text } : SceneLabel))
    have htitle (metric : Measure.Metric) :
        title metric (emit (rootInput inp)) = title metric (emit inp) := by
      rw [hEmit]
      funext model
      have hfind :
          ((emit inp).map rootBox).find? (fun b => b.id == model.owner && !b.exclusive) =
            ((emit inp).find? (fun b => b.id == model.owner && !b.exclusive)).map rootBox := by
        rw [List.find?_map] <;> rfl
      dsimp only [title]
      rw [hfind]
      cases (emit inp).find? (fun b => b.id == model.owner && !b.exclusive) <;> rfl
    cases hm : metricOf o.profile o.fontFamily with
    | error e => rfl
    | ok metric =>
      simp only [hlabel]
      have ht :
          (rootInput inp).labels.filterMapM (title metric (emit (rootInput inp))) =
            inp.labels.filterMapM (title metric (emit inp)) :=
        congrArg (fun f => inp.labels.filterMapM f) (htitle metric)
      simp only [title, emit, part, bind, Except.bind] at ht
      erw [ht]
      split
      · rename_i hts
        erw [hts] <;> rfl
      · rename_i hts
        erw [hts]
        apply erase_expandedCost P inp o
        have he := hEqErase
        dsimp only [emit, part] at he
        dsimp only [eraseParents]
        erw [he] <;> rfl

private theorem erase_trial (P : Params) (exactIds : List String) (spec : Option RegionSpec)
    (inp : Input) (o : Options) (g : Graph) (comp : List Nat) (labels : List MeasuredLabel)
    (index : Nat) :
    (componentTrialR P exactIds spec (rootInput inp) o g comp labels index).map eraseCandidate =
      (componentTrialR P exactIds spec inp o g comp labels index).map eraseCandidate := by
  unfold componentTrialR
  simp only [rooted_newComponentRegions, rooted_exactDecls, rooted_componentRunR]
  cases newComponentRegions spec P inp (componentGraph g comp) with
  | error e => rfl
  | ok rs =>
    simp only [bind, Except.bind]
    let effective := if rs.isSome then spec else none
    let cg := componentCandidateR effective g comp index
    cases componentRunR P (exactDecls exactIds inp) effective inp cg labels (candidateOrder index) with
    | error e => rfl
    | ok pair =>
      obtain ⟨chosen, run⟩ := pair
      have hs := erase_componentScene P inp o chosen run labels
      try dsimp only
      cases ha : componentScene P (rootInput inp) o chosen run labels (@placeComponentExact) with
      | error ea =>
        cases hb : componentScene P inp o chosen run labels (@placeComponentExact) with
        | error eb =>
          have he : ea = eb := Except.error.inj (by simpa only [ha, hb, Except.map] using hs)
          subst eb
          rfl
        | ok b => simp [ha, hb, Except.map] at hs
      | ok a =>
        cases hb : componentScene P inp o chosen run labels (@placeComponentExact) with
        | error eb => simp [ha, hb, Except.map] at hs
        | ok b =>
          have he : eraseParents a = eraseParents b :=
            Except.ok.inj (by simpa only [ha, hb, Except.map] using hs)
          exact congrArg (fun s => Except.ok
            (⟨(chosen, run), s, run.budget⟩ : Portfolio.Candidate (Graph × Run))) he

@[simp] theorem rooted_layoutComponent (P : Params) (exactIds : List String) (spec : Option RegionSpec)
    (inp : Input) (o : Options) (g : Graph) (acc : Acc) (comp : List Nat) (labels : List MeasuredLabel) :
    layoutComponentR P exactIds spec (rootInput inp) o g acc comp labels =
      layoutComponentR P exactIds spec inp o g acc comp labels := by
  let trial := componentTrialR P exactIds spec inp o g comp labels
  let rooted := componentTrialR P exactIds spec (rootInput inp) o g comp labels
  have htrial : (fun i => (rooted i).map eraseCandidate) = fun i => (trial i).map eraseCandidate :=
    funext (erase_trial P exactIds spec inp o g comp labels)
  have h := ((erase_portfolio rooted o.thoroughness).symm.trans
    ((congrArg (Portfolio.portfolio o.thoroughness) htrial).trans (erase_portfolio trial o.thoroughness)))
  have hbody (a b : Portfolio.Candidate (Graph × Run)) (he : eraseCandidate a = eraseCandidate b) :
      a.value = b.value ∧ a.budgetExhausted = b.budgetExhausted ∧
        a.scene.boxes.map Box.id = b.scene.boxes.map Box.id := by
    have hv : (eraseCandidate a).value = (eraseCandidate b).value :=
      congrArg Portfolio.Candidate.value he
    have hbudget : (eraseCandidate a).budgetExhausted = (eraseCandidate b).budgetExhausted :=
      congrArg Portfolio.Candidate.budgetExhausted he
    have hids (c : Portfolio.Candidate (Graph × Run)) :
        (eraseCandidate c).scene.boxes.map Box.id = c.scene.boxes.map Box.id := by
      change (c.scene.boxes.map eraseParent).map Box.id = _
      rw [List.map_map] <;> rfl
    have hi := congrArg (fun c : Portfolio.Candidate (Graph × Run) => c.scene.boxes.map Box.id) he
    exact ⟨hv, hbudget, (hids a).symm.trans (hi.trans (hids b))⟩
  unfold layoutComponentR
  cases ha : Portfolio.portfolio o.thoroughness rooted <;>
    cases hb : Portfolio.portfolio o.thoroughness trial
  · rename_i a b
    have he : a = b := Except.error.inj (by simpa only [ha, hb, Except.map] using h)
    subst b
    rfl
  · simp [ha, hb, Except.map] at h
  · simp [ha, hb, Except.map] at h
  · rename_i a b
    have he : eraseCandidate a = eraseCandidate b :=
      Except.ok.inj (by simpa only [ha, hb, Except.map] using h)
    obtain ⟨hv, hbudget, hboxes⟩ := hbody a b he
    have hany (id : String) : a.scene.boxes.any (fun box => box.id == id) =
        b.scene.boxes.any (fun box => box.id == id) := by
      simpa only [List.any_map, Function.comp_def] using congrArg (fun ids => ids.any (· == id)) hboxes
    simp only [bind, Except.bind, hv, hbudget, rootInput,
      List.zipIdx_map, List.filter_map, List.mapM_map, Function.comp_def, hany] <;> rfl

end Elegant.Layered.PipelineImpl.ContractedC8a
