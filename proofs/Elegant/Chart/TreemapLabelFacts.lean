import Elegant.Kinds.Treemap

namespace Elegant.Treemap.LabelFacts

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem conditional_bind_ok {α β : Type} {p : Prop} [Decidable p]
    {yes no : Except LayoutError α} {f : α → Except LayoutError β} {out : β}
    (h : (if p then yes >>= f else no >>= f) = .ok out) :
    ∃ a, (if p then yes else no) = .ok a ∧ f a = .ok out := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte] at h ⊢
    exact bind_ok h
  · simp only [hp, ↓reduceIte] at h ⊢
    exact bind_ok h

def sources (ls : List PlacedLabel) : List ModelLabel := ls.map (·.source)

@[simp] theorem putLabel_source (l : PlacedLabel) (shown : String) (r : Rect)
    (size : Int) : (putLabel l shown r size).source = l.source := rfl

theorem sources_modify (ls : List PlacedLabel) (i : Nat)
    (f : PlacedLabel → PlacedLabel) (hf : ∀ l, (f l).source = l.source) :
    sources (ls.modify i f) = sources ls := by
  induction ls generalizing i with
  | nil => cases i <;> rfl
  | cons l ls ih =>
    cases i with
    | zero => simp [sources, List.modify, hf]
    | succ i => simpa [sources, List.modify] using congrArg (List.cons l.source) (ih i)

@[simp] theorem initialLabels_sources (m : Model) :
    sources (initialLabels m) = m.labels := by
  simp only [initialLabels, sources, List.map_map]
  have hf : (fun l : ModelLabel =>
      (if l.id == "title" then ({ source := l, role := .title } : PlacedLabel)
       else if l.id.endsWith ".value" then
         { source := l, role := .body, style := "text-muted" }
       else { source := l }).source) = id := by
    funext l
    split <;> first | rfl | (split <;> rfl)
  change List.map
    (fun l : ModelLabel =>
      (if l.id == "title" then ({ source := l, role := .title } : PlacedLabel)
       else if l.id.endsWith ".value" then
         { source := l, role := .body, style := "text-muted" }
       else { source := l }).source) m.labels = m.labels
  rw [hf]
  exact List.map_id m.labels

theorem placeTitle_sources (m : Model) (c : Consts)
    (before after : List PlacedLabel)
    (h : placeTitle m c before = .ok after) : sources after = sources before := by
  unfold placeTitle at h
  repeat' first
    | split at h
    | simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals cases h
  all_goals
    repeat' first
      | rfl
      | (apply Eq.trans
         · apply sources_modify
           intro l
           rfl)

theorem placeHeader_sources (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel)
    (h : placeHeader m c n before = .ok after) : sources after = sources before := by
  unfold placeHeader at h
  repeat' first
    | split at h
    | simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals cases h
  all_goals
    repeat' first
      | rfl
      | (apply Eq.trans
         · apply sources_modify
           intro l
           rfl)

theorem placeLeaf_sources (m : Model) (lc : LeafConsts) (n : Node)
    (before after : List PlacedLabel)
    (h : placeLeaf m lc n before = .ok after) : sources after = sources before := by
  unfold placeLeaf at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases hcell : (m.profile == Profile.cell) = true
  all_goals simp only [hcell, ↓reduceIte] at h
  all_goals
    by_cases hsmall :
      (tileRect n.rect).w - 2 * lc.pad < lc.minDisplay ∨
      (tileRect n.rect).h - 2 * lc.pad < lc.minDisplay
  all_goals simp only [hsmall, ↓reduceIte] at h
  all_goals
    repeat' first
      | (obtain ⟨intermediate, hintermediate, h⟩ := bind_ok h)
      | split at h
      | simp only [pure, Except.pure] at h
  all_goals cases h
  all_goals
    repeat' first
      | rfl
      | (apply Eq.trans
         · apply sources_modify
           intro l
           rfl)

def step (m : Model) (nodes : List Node) (lc : LeafConsts)
    (ls : List PlacedLabel) (n : Node) : Except LayoutError (List PlacedLabel) :=
  if n.source.id == "root" then pure ls
  else if (children nodes n.source.id).isEmpty then placeLeaf m lc n ls
  else placeHeader m (constants m) n ls

theorem step_sources (m : Model) (nodes : List Node) (lc : LeafConsts)
    (n : Node) (before after : List PlacedLabel)
    (h : step m nodes lc before n = .ok after) : sources after = sources before := by
  unfold step at h
  split at h
  · cases h; rfl
  · split at h
    · exact placeLeaf_sources m lc n before after h
    · exact placeHeader_sources m (constants m) n before after h

theorem fold_sources (m : Model) (nodes todo : List Node) (lc : LeafConsts)
    (before after : List PlacedLabel)
    (h : todo.foldlM (step m nodes lc) before = .ok after) :
    sources after = sources before := by
  induction todo generalizing before with
  | nil => cases h; rfl
  | cons n ns ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨middle, hs, ht⟩ := bind_ok h
    exact (ih middle ht).trans (step_sources m nodes lc n before middle hs)

def denseConstants (m : Model) (nodes : List Node) : LeafConsts :=
  leafConstants m.profile
    (nodes.countP (fun n => n.source.id != "root" && (children nodes n.source.id).isEmpty) >
      (LayoutConst.treemap_dense_leaves.get m.profile).toNat)

def seededNodes (m : Model) : List Node :=
  (assignSeries (aggregate (initialNodes m))).map fun n =>
    if n.source.id == "root" then
      { n with rect := ⟨0,
        if (labelText m "title").isEmpty then 0 else (constants m).titleBand,
        (constants m).width,
        (if (labelText m "title").isEmpty then 0 else (constants m).titleBand) +
          (constants m).height⟩ }
    else n

def dumpLabel (l : PlacedLabel) : SceneLabel :=
  { id := l.source.id, owner := l.source.owner, rect := l.rect,
    lines := if l.visible then [l.shown] else [], text := l.source.text }

theorem layout_label_execution (m : Model) (scene : Scene)
    (h : Elegant.Treemap.layout m = .ok scene) :
    ∃ nodes titleLabels finalLabels,
      tileNodes (constants m) (seededNodes m) = .ok nodes ∧
      placeTitle m (constants m) (initialLabels m) = .ok titleLabels ∧
      nodes.foldlM (step m nodes (denseConstants m nodes)) titleLabels = .ok finalLabels ∧
      sources titleLabels = m.labels ∧ sources finalLabels = m.labels ∧
      scene.labels = finalLabels.map dumpLabel := by
  unfold Elegant.Treemap.layout at h
  dsimp only at h
  obtain ⟨nodes, hn, h⟩ := bind_ok h
  split at h
  · cases h
  · obtain ⟨titleLabels, ht, h⟩ := bind_ok h
    obtain ⟨finalLabels, hf, h⟩ := bind_ok h
    generalize hband :
      (if (labelText m "title").isEmpty then 0 else (constants m).titleBand) = band at h
    split at h
    · simp only [bind, Except.bind, pure, Except.pure] at h
      cases h
    · simp only [pure, Except.pure] at h
      injection h with heq
      subst scene
      have htSources := (placeTitle_sources m (constants m) (initialLabels m)
        titleLabels ht).trans (initialLabels_sources m)
      have hfSources := (fold_sources m nodes nodes (denseConstants m nodes)
        titleLabels finalLabels hf).trans htSources
      exact ⟨nodes, titleLabels, finalLabels, hn, ht, hf, htSources, hfSources, rfl⟩

theorem public_label_execution (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) :
    ∃ nodes titleLabels finalLabels,
      tileNodes (constants m) (seededNodes m) = .ok nodes ∧
      placeTitle m (constants m) (initialLabels m) = .ok titleLabels ∧
      nodes.foldlM (step m nodes (denseConstants m nodes)) titleLabels = .ok finalLabels ∧
      sources titleLabels = m.labels ∧ sources finalLabels = m.labels ∧
      result.scene.labels = finalLabels.map dumpLabel :=
  layout_label_execution m result.scene (Kinds.Treemap.layout_adapter_success m result h)

theorem source_at_index (m : Model) (ls : List PlacedLabel)
    (hs : sources ls = m.labels) (i : Nat) :
    (ls[i]?).map (·.source) = m.labels[i]? := by
  simpa [sources] using congrArg (fun xs : List ModelLabel => xs[i]?) hs

theorem dumpLabel_identity (l : PlacedLabel) :
    (dumpLabel l).id = l.source.id ∧
    (dumpLabel l).owner = l.source.owner ∧
    (dumpLabel l).text = l.source.text ∧
    (dumpLabel l).rect = l.rect ∧
    (dumpLabel l).lines = (if l.visible then [l.shown] else []) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem placeTitle_cases (m : Model) (c : Consts)
    (before after : List PlacedLabel)
    (h : placeTitle m c before = .ok after) :
    after = before ∨
      ∃ i l shown w,
        before.findIdx? (fun x => x.source.id == "title") = some i ∧
        before[i]? = some l ∧
        fit (fontFamily := m.options.fontFamily) (m.profile == .cell) l.source.text c.width .title 16 = .ok (some (shown, w)) ∧
        after = before.modify i (fun old => putLabel old shown
          ⟨Int.fdiv (c.width - w) 2,
            Int.fdiv (c.titleBand - (if m.profile == .cell then 1 else 1536)) 2,
            w, if m.profile == .cell then 1 else 1536⟩ 16) := by
  unfold placeTitle at h
  split at h
  · cases h; exact Or.inl rfl
  · rename_i i hi
    split at h
    · cases h; exact Or.inl rfl
    · rename_i l hl
      cases hfit : fit (fontFamily := m.options.fontFamily) (m.profile == .cell) l.source.text c.width .title 16 with
      | error e =>
        simp only [hfit, bind, Except.bind] at h
        cases h
      | ok answer =>
        cases answer with
        | none =>
          simp only [hfit, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          exact Or.inl h.symm
        | some pair =>
          obtain ⟨shown, w⟩ := pair
          simp only [hfit, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          exact Or.inr ⟨i, l, shown, w, hi, hl, hfit, h.symm⟩

theorem fold_cons_execution (m : Model) (nodes : List Node) (lc : LeafConsts)
    (n : Node) (todo : List Node) (before after : List PlacedLabel)
    (h : (n :: todo).foldlM (step m nodes lc) before = .ok after) :
    ∃ middle,
      step m nodes lc before n = .ok middle ∧
      todo.foldlM (step m nodes lc) middle = .ok after ∧
      sources middle = sources before := by
  rw [List.foldlM_cons] at h
  obtain ⟨middle, hs, ht⟩ := bind_ok h
  exact ⟨middle, hs, ht, step_sources m nodes lc n before middle hs⟩

theorem step_cases (m : Model) (nodes : List Node) (lc : LeafConsts)
    (n : Node) (before after : List PlacedLabel)
    (h : step m nodes lc before n = .ok after) :
    ((n.source.id == "root") = true ∧ after = before) ∨
    ((n.source.id == "root") = false ∧
      (children nodes n.source.id).isEmpty = true ∧
      placeLeaf m lc n before = .ok after) ∨
    ((n.source.id == "root") = false ∧
      (children nodes n.source.id).isEmpty = false ∧
      placeHeader m (constants m) n before = .ok after) := by
  unfold step at h
  cases hid : (n.source.id == "root") with
  | true =>
    simp only [hid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨rfl, h.symm⟩
  | false =>
    cases hc : (children nodes n.source.id).isEmpty with
    | true =>
      simp only [hid, hc, Bool.false_eq_true, ↓reduceIte] at h
      exact Or.inr (Or.inl ⟨rfl, rfl, h⟩)
    | false =>
      simp only [hid, hc, Bool.false_eq_true, ↓reduceIte] at h
      exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)

theorem fit_success_cases {fontFamily : Bool} (cell : Bool) (text : String) (avail : Int)
    (role : Measure.Role) (size : Int) (shown : String) (w : Int)
    (h : fit (fontFamily := fontFamily) cell text avail role size = .ok (some (shown, w))) :
    text.isEmpty = false ∧
      ((shown = text ∧ width (fontFamily := fontFamily) cell text role size = .ok w ∧ w ≤ avail) ∨
        width (fontFamily := fontFamily) cell shown role size = .ok w) := by
  unfold fit at h
  cases he : text.isEmpty with
  | true =>
    simp only [he, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    cases h
  | false =>
    simp only [he, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨originalWidth, hw, h⟩ := bind_ok h
    split at h
    · rename_i hbound
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hs, hw'⟩ := h
      subst shown
      subst w
      exact ⟨rfl, Or.inl ⟨rfl, hw, hbound⟩⟩
    · obtain ⟨ellipsisWidth, _, h⟩ := bind_ok h
      split at h
      · cases h
      · obtain ⟨k, _, h⟩ := bind_ok h
        obtain ⟨shownWidth, hshown, h⟩ := bind_ok h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨hs, hw'⟩ := h
        subst shown
        subst w
        exact ⟨rfl, Or.inr hshown⟩

theorem putLabel_placement (l : PlacedLabel) (shown : String) (r : Rect)
    (size : Int) :
    (putLabel l shown r size).source = l.source ∧
    (putLabel l shown r size).shown = shown ∧
    (putLabel l shown r size).rect = r ∧
    (putLabel l shown r size).size = size ∧
    (putLabel l shown r size).visible = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem public_label_identity_at_index (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) (i : Nat) :
    (result.scene.labels[i]?).map (fun l => (l.id, l.owner, l.text)) =
      (m.labels[i]?).map (fun l => (l.id, l.owner, l.text)) := by
  obtain ⟨_, _, finalLabels, _, _, _, _, hs, hd⟩ :=
    public_label_execution m result h
  have hi := source_at_index m finalLabels hs i
  rw [hd]
  simpa [List.getElem?_map, Option.map_map, Function.comp_def, dumpLabel] using
    congrArg (Option.map (fun l : ModelLabel => (l.id, l.owner, l.text))) hi

theorem modified_label_at_index (before : List PlacedLabel) (i j : Nat)
    (f : PlacedLabel → PlacedLabel) :
    (before.modify j f)[i]? =
      (before[i]?).map (fun l => if j = i then f l else l) :=
  List.getElem?_modify f j before i

theorem name_value_writes_at_index (before middle after : List PlacedLabel)
    (name value i : Nat) (writeName writeValue : PlacedLabel → PlacedLabel)
    (hn : middle = before.modify name writeName)
    (hv : after = middle.modify value writeValue) :
    after[i]? = (before[i]?).map (fun l =>
      if value = i then writeValue (if name = i then writeName l else l)
      else if name = i then writeName l else l) := by
  subst after
  subst middle
  simp only [List.getElem?_modify, Option.map_eq_map, Option.map_map, Function.comp_def]

theorem placeHeader_skip_height (m : Model) (c : Consts) (n : Node)
    (before : List PlacedLabel)
    (hskip : (tileRect n.rect).h ≤
      LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
          (if m.profile == .cell then 1 else 1280)) 2 +
        (if m.profile == .cell then 1 else 1280)) :
    placeHeader m c n before = .ok before := by
  unfold placeHeader
  simp only [hskip, ↓reduceIte, pure, Except.pure]

theorem placeLeaf_skip_name (m : Model) (lc : LeafConsts) (n : Node)
    (before : List PlacedLabel)
    (hname : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = none) :
    placeLeaf m lc n before = .ok before := by
  unfold placeLeaf
  change (match before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") with
    | none => _
    | some _ => _) = _
  rw [hname]
  rfl

theorem placeLeaf_cell_fit_cases (m : Model) (lc : LeafConsts) (n : Node)
    (before after : List PlacedLabel) (j : Nat)
    (hcell : (m.profile == .cell) = true)
    (hname : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = some j)
    (hdisplay : ¬((tileRect n.rect).w - 2 * lc.pad < lc.minDisplay ∨
      (tileRect n.rect).h - 2 * lc.pad < lc.minDisplay))
    (h : placeLeaf m lc n before = .ok after) :
    let r := tileRect n.rect
    let aw := r.w - 2 * lc.pad
    let ah := r.h - 2 * lc.pad
    let value := before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
    let nameText := ((before[j]?).map (·.source.text)).getD ""
    let valueText := ((value.bind fun k => before[k]?).map (·.source.text)).getD ""
    (fit (fontFamily := m.options.fontFamily) true nameText aw .label 0 = .ok none ∧ after = before) ∨
      ∃ shown nw vw middle,
        fit (fontFamily := m.options.fontFamily) true nameText aw .label 0 = .ok (some (shown, nw)) ∧
        (if value.isSome && decide (2 + lc.spacing ≤ ah) then
          width (fontFamily := m.options.fontFamily) true valueText .body 0 else pure 0) = .ok vw ∧
        let showValue := value.isSome && decide (2 + lc.spacing ≤ ah) && decide (vw ≤ aw)
        let rows := if showValue then 2 + lc.spacing else 1
        let top := r.y + lc.pad + Int.fdiv (ah - rows) 2
        middle = before.modify j (fun l => putLabel l shown
          ⟨r.x + lc.pad + Int.fdiv (aw - nw) 2, top, nw, 1⟩ 0) ∧
        after = (if showValue then
          match value with
          | none => middle
          | some k => middle.modify k (fun l => putLabel l l.source.text
              ⟨r.x + lc.pad + Int.fdiv (aw - vw) 2, top + 1 + lc.spacing, vw, 1⟩ 0)
          else middle) := by
  dsimp only
  unfold placeLeaf at h
  change (match before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") with
    | none => _
    | some _ => _) = _ at h
  rw [hname] at h
  simp only [labelIndex_eq_findIdx, sourceText_eq_lookup] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, hdisplay, hcell, ↓reduceIte,
    pure, Except.pure, bind, Except.bind] at h
  change (fit (fontFamily := m.options.fontFamily) true
      ((((before.findIdx? (fun l => l.source.id == n.source.id ++ ".name")).bind
        fun k => before[k]?).map (·.source.text)).getD "")
      ((tileRect n.rect).w - 2 * lc.pad) .label 0 >>= _) = .ok after at h
  obtain ⟨answer, hfit, h⟩ := bind_ok h
  change fit (fontFamily := m.options.fontFamily) true
    ((((before.findIdx? (fun l => l.source.id == n.source.id ++ ".name")).bind
      fun k => before[k]?).map (·.source.text)).getD "")
    _ _ _ = _ at hfit
  rw [hname] at hfit
  cases answer with
  | none =>
    left
    refine ⟨hfit, ?_⟩
    change Except.ok before = Except.ok after at h
    exact Except.ok.inj h.symm
  | some pair =>
    obtain ⟨shown, nw⟩ := pair
    dsimp only at h
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Int.mul_one] at h
    by_cases hmeasure :
        ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
          decide (2 + lc.spacing ≤ (tileRect n.rect).h - 2 * lc.pad)) = true
    · simp only [hmeasure, ↓reduceIte] at h
      obtain ⟨vw, hvw, h⟩ := bind_ok h
      right
      refine ⟨shown, nw, vw, _, hfit, ?_, rfl, ?_⟩
      · simpa only [hmeasure, ↓reduceIte] using hvw
      · by_cases hs : decide (vw ≤ (tileRect n.rect).w - 2 * lc.pad) = true
        · simp only [hmeasure, Bool.true_and, hs, ↓reduceIte] at h ⊢
          cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
          | none =>
            simp only [hv] at h ⊢
            exact (Except.ok.inj h).symm
          | some k =>
            simp only [hv] at h ⊢
            exact (Except.ok.inj h).symm
        · simp only [hmeasure, Bool.true_and, hs] at h ⊢
          exact (Except.ok.inj h).symm
    · simp only [hmeasure, Bool.false_eq_true, ↓reduceIte] at h
      right
      refine ⟨shown, nw, 0, _, hfit, ?_, rfl, ?_⟩
      · simp only [hmeasure, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
      · simp only [hmeasure, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact (Except.ok.inj h).symm

theorem placeHeader_fit_cases (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel) (j : Nat)
    (hname : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = some j)
    (hheight : ¬((tileRect n.rect).h ≤
      LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
          (if m.profile == .cell then 1 else 1280)) 2 +
        (if m.profile == .cell then 1 else 1280)))
    (h : placeHeader m c n before = .ok after) :
    let p := m.profile
    let cell := p == .cell
    let r := tileRect n.rect
    let value := before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
    let nameText := ((before[j]?).map (·.source.text)).getD ""
    let valueText := ((value.bind fun k => before[k]?).map (·.source.text)).getD ""
    let ns := Int.fdiv (LayoutConst.treemap_header_label_size.get p) 64
    let vs := Int.fdiv (LayoutConst.treemap_header_value_size.get p) 64
    let lh := if cell then 1 else 1280
    let border := LayoutConst.treemap_header_border.get p
    let top := border + Int.fdiv (c.header - border - lh) 2
    let vi := LayoutConst.treemap_header_value_inset.get p
    let ni := LayoutConst.treemap_header_label_inset.get p
    ∃ vw fitted middle,
      (if value.isSome then width (fontFamily := m.options.fontFamily) cell valueText .body vs else pure 0) = .ok vw ∧
      let reserve := vi + vw + LayoutConst.treemap_header_gap.get p
      let showValue := value.isSome && decide (vw + vi + ni ≤ r.w) &&
        decide (r.w - ni - reserve ≥ LayoutConst.treemap_header_label_min.get p)
      let avail := if showValue then r.w - ni - reserve else r.w - 2 * ni
      fit (fontFamily := m.options.fontFamily) cell nameText avail .label ns = .ok fitted ∧
      middle = (match fitted with
        | none => before
        | some (shown, w) => before.modify j (fun l =>
          { putLabel l shown ⟨r.x + ni, r.y + top, w, lh⟩ ns with align := .start })) ∧
      after = (if showValue then
        match value with
        | none => middle
        | some k => middle.modify k (fun l =>
          { putLabel l l.source.text ⟨r.x + r.w - vi - vw, r.y + top, vw, lh⟩ vs
            with align := .«end», italic := true })
        else middle) := by
  dsimp only
  unfold placeHeader at h
  simp only [labelIndex_eq_findIdx, sourceText_eq_lookup] at h
  change (if (tileRect n.rect).h ≤
      LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
          (if m.profile == .cell then 1 else 1280)) 2 +
        (if m.profile == .cell then 1 else 1280) then _ else _) = _ at h
  rw [ite_eq_right hheight] at h
  obtain ⟨vw, hvw, h⟩ := conditional_bind_ok h
  change (match before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") with
    | none => _
    | some _ => _) = _ at h
  simp only [hname] at h
  obtain ⟨fitted, hfit, h⟩ := bind_ok h
  simp only [Option.bind_some, Option.isNone_some, Bool.false_or] at hfit h
  refine ⟨vw, fitted, _, hvw, hfit, rfl, ?_⟩
  · cases fitted with
    | none =>
      split <;> rename_i hs
      · simp only [hs, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
        cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
        | none =>
          simp only [hv] at h ⊢
          exact (Except.ok.inj h).symm
        | some k =>
          simp only [hv] at h ⊢
          exact (Except.ok.inj h).symm
      · simp only [hs, bind, Except.bind, pure, Except.pure] at h
        exact (Except.ok.inj h).symm
    | some pair =>
      obtain ⟨shown, w⟩ := pair
      split <;> rename_i hs
      · simp only [hs, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
        cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
        | none =>
          simp only [hv] at h ⊢
          exact (Except.ok.inj h).symm
        | some k =>
          simp only [hv] at h ⊢
          exact (Except.ok.inj h).symm
      · simp only [hs, bind, Except.bind, pure, Except.pure] at h
        exact (Except.ok.inj h).symm

theorem placeHeader_absent_name_cases (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel)
    (hname : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = none)
    (hheight : ¬((tileRect n.rect).h ≤
      LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
          (if m.profile == .cell then 1 else 1280)) 2 +
        (if m.profile == .cell then 1 else 1280)))
    (h : placeHeader m c n before = .ok after) :
    let p := m.profile
    let cell := p == .cell
    let r := tileRect n.rect
    let value := before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
    let valueText := ((value.bind fun k => before[k]?).map (·.source.text)).getD ""
    let vs := Int.fdiv (LayoutConst.treemap_header_value_size.get p) 64
    let lh := if cell then 1 else 1280
    let border := LayoutConst.treemap_header_border.get p
    let top := border + Int.fdiv (c.header - border - lh) 2
    let vi := LayoutConst.treemap_header_value_inset.get p
    let ni := LayoutConst.treemap_header_label_inset.get p
    ∃ vw,
      (if value.isSome then width (fontFamily := m.options.fontFamily) cell valueText .body vs else pure 0) = .ok vw ∧
      after = (if value.isSome && decide (vw + vi + ni ≤ r.w) then
        match value with
        | none => before
        | some k => before.modify k (fun l =>
          { putLabel l l.source.text ⟨r.x + r.w - vi - vw, r.y + top, vw, lh⟩ vs
            with align := .«end», italic := true })
        else before) := by
  dsimp only
  unfold placeHeader at h
  simp only [labelIndex_eq_findIdx, sourceText_eq_lookup] at h
  rw [ite_eq_right hheight] at h
  obtain ⟨vw, hvw, h⟩ := conditional_bind_ok h
  simp only [hname, Option.isNone_none, Bool.true_or, Bool.and_true,
    bind, Except.bind, pure, Except.pure] at h
  refine ⟨vw, hvw, ?_⟩
  split <;> rename_i hs
  · simp only [hs, ↓reduceIte] at h
    cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
    | none =>
      simp only [hv] at h ⊢
      exact (Except.ok.inj h).symm
    | some k =>
      simp only [hv] at h ⊢
      exact (Except.ok.inj h).symm
  · simp only [hs] at h
    exact (Except.ok.inj h).symm

theorem placeLeaf_skip_display (m : Model) (lc : LeafConsts) (n : Node)
    (before : List PlacedLabel)
    (hskip : (tileRect n.rect).w - 2 * lc.pad < lc.minDisplay ∨
      (tileRect n.rect).h - 2 * lc.pad < lc.minDisplay) :
    placeLeaf m lc n before = .ok before := by
  unfold placeLeaf
  simp only [Bool.or_eq_true, decide_eq_true_eq, hskip, ↓reduceIte]
  split <;> rfl

theorem placeLeaf_vector_fit_cases (m : Model) (lc : LeafConsts) (n : Node)
    (before after : List PlacedLabel) (j : Nat)
    (hcell : (m.profile == .cell) = false)
    (hname : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = some j)
    (hdisplay : ¬((tileRect n.rect).w - 2 * lc.pad < lc.minDisplay ∨
      (tileRect n.rect).h - 2 * lc.pad < lc.minDisplay))
    (h : placeLeaf m lc n before = .ok after) :
    let r := tileRect n.rect
    let aw := r.w - 2 * lc.pad
    let value := before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
    let nameText := ((before[j]?).map (·.source.text)).getD ""
    let valueText := ((value.bind fun k => before[k]?).map (·.source.text)).getD ""
    ∃ ns,
      (fit (fontFamily := m.options.fontFamily) false nameText aw .label ns = .ok none ∧ after = before) ∨
      ∃ shown nw,
        fit (fontFamily := m.options.fontFamily) false nameText aw .label ns = .ok (some (shown, nw)) ∧
        ((1280 > r.h ∧ after = before) ∨
        ∃ vw middle,
          ¬1280 > r.h ∧
          let vs := max (Int.fdiv lc.valueMin 64)
            (min (Int.fdiv lc.valueSize 64)
              (roundDiv (ns * LayoutConst.treemap_value_scale_percent.get m.profile) 100))
          (if value.isSome && decide (2 * 1280 + lc.spacing ≤ r.h) then
            width (fontFamily := m.options.fontFamily) false valueText .body vs else pure 0) = .ok vw ∧
          let showValue := value.isSome && decide (2 * 1280 + lc.spacing ≤ r.h) &&
            decide (vw ≤ aw)
          let rows := if showValue then 2 * 1280 + lc.spacing else 1280
          let top := r.y + Int.fdiv (r.h - rows) 2
          middle = before.modify j (fun l => putLabel l shown
            ⟨r.x + lc.pad + Int.fdiv (aw - nw) 2, top, nw, 1280⟩ ns) ∧
          after = (if showValue then
            match value with
            | none => middle
            | some k => middle.modify k (fun l => putLabel l l.source.text
                ⟨r.x + lc.pad + Int.fdiv (aw - vw) 2,
                  top + 1280 + lc.spacing, vw, 1280⟩ vs)
            else middle)) := by
  dsimp only
  unfold placeLeaf at h
  simp only [labelIndex_eq_findIdx, sourceText_eq_lookup] at h
  simp only [hname, Bool.or_eq_true, decide_eq_true_eq, hdisplay, hcell,
    Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨ns, _hsize, h⟩ := bind_ok h
  obtain ⟨fitted, hfit, h⟩ := bind_ok h
  refine ⟨ns, ?_⟩
  cases fitted with
  | none =>
    left
    exact ⟨hfit, (Except.ok.inj h).symm⟩
  | some pair =>
    obtain ⟨shown, nw⟩ := pair
    right
    refine ⟨shown, nw, hfit, ?_⟩
    dsimp only at h
    by_cases hshort : 1280 > (tileRect n.rect).h
    · left
      simp only [Bool.not_false, Bool.true_and, hshort] at h
      exact ⟨hshort, (Except.ok.inj h).symm⟩
    · right
      simp only [Bool.not_false, Bool.true_and, hshort] at h
      by_cases hmeasure :
          ((before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")).isSome &&
            decide (2 * 1280 + lc.spacing ≤ (tileRect n.rect).h)) = true
      · simp only [hmeasure, ↓reduceIte] at h
        obtain ⟨vw, hvw, h⟩ := bind_ok h
        refine ⟨vw, _, hshort, ?_, rfl, ?_⟩
        · simpa only [hmeasure, ↓reduceIte] using hvw
        · by_cases hs : decide (vw ≤ (tileRect n.rect).w - 2 * lc.pad) = true
          · simp only [hmeasure, Bool.true_and, hs, ↓reduceIte] at h ⊢
            cases hv : before.findIdx? (fun l => l.source.id == n.source.id ++ ".value") with
            | none =>
              simp only [hv] at h ⊢
              exact (Except.ok.inj h).symm
            | some k =>
              simp only [hv] at h ⊢
              exact (Except.ok.inj h).symm
          · simp only [hmeasure, Bool.true_and, hs] at h ⊢
            exact (Except.ok.inj h).symm
      · simp only [hmeasure, Bool.false_eq_true, ↓reduceIte] at h
        refine ⟨0, _, hshort, ?_, rfl, ?_⟩
        · simp only [hmeasure, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
        · simp only [hmeasure, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact (Except.ok.inj h).symm

inductive IndexStableRun (m : Model) (nodes : List Node) (lc : LeafConsts)
    (i : Nat) : List Node → List PlacedLabel → List PlacedLabel → Prop where
  | nil (labels) : IndexStableRun m nodes lc i [] labels labels
  | cons {n todo before middle after}
      (head : step m nodes lc before n = .ok middle)
      (unchanged : middle[i]? = before[i]?)
      (tail : IndexStableRun m nodes lc i todo middle after) :
      IndexStableRun m nodes lc i (n :: todo) before after

theorem IndexStableRun.index_eq {m : Model} {nodes : List Node} {lc : LeafConsts}
    {i : Nat} {todo : List Node} {before after : List PlacedLabel}
    (h : IndexStableRun m nodes lc i todo before after) :
    after[i]? = before[i]? := by
  induction h with
  | nil => rfl
  | cons _ unchanged _ ih => exact ih.trans unchanged

theorem fold_last_index_change (m : Model) (nodes todo : List Node)
    (lc : LeafConsts) (before after : List PlacedLabel) (i : Nat)
    (h : todo.foldlM (step m nodes lc) before = .ok after) :
    IndexStableRun m nodes lc i todo before after ∨
      ∃ prior n suffix lastBefore lastAfter,
        todo = prior ++ n :: suffix ∧
        prior.foldlM (step m nodes lc) before = .ok lastBefore ∧
        step m nodes lc lastBefore n = .ok lastAfter ∧
        lastAfter[i]? ≠ lastBefore[i]? ∧
        IndexStableRun m nodes lc i suffix lastAfter after := by
  induction todo generalizing before with
  | nil =>
    have heq : before = after := Except.ok.inj h
    subst after
    exact Or.inl (.nil before)
  | cons n todo ih =>
    obtain ⟨middle, hs, ht, _⟩ := fold_cons_execution m nodes lc n todo before after h
    rcases ih middle ht with stable | ⟨prior, last, suffix, lb, la, heq, hp, hl, hc, hr⟩
    · by_cases hi : middle[i]? = before[i]?
      · exact Or.inl (.cons hs hi stable)
      · exact Or.inr ⟨[], n, todo, before, middle, rfl, rfl, hs, hi, stable⟩
    · right
      refine ⟨n :: prior, last, suffix, lb, la, ?_, ?_, hl, hc, hr⟩
      · simp only [List.cons_append, heq]
      · rw [List.foldlM_cons]
        simp only [hs, bind, Except.bind]
        exact hp

theorem public_last_label_placement (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) (i : Nat) :
    ∃ nodes titleLabels finalLabels,
      tileNodes (constants m) (seededNodes m) = .ok nodes ∧
      placeTitle m (constants m) (initialLabels m) = .ok titleLabels ∧
      sources titleLabels = m.labels ∧ sources finalLabels = m.labels ∧
      result.scene.labels = finalLabels.map dumpLabel ∧
      (IndexStableRun m nodes (denseConstants m nodes) i nodes titleLabels finalLabels ∨
        ∃ prior n suffix lastBefore lastAfter,
          nodes = prior ++ n :: suffix ∧
          prior.foldlM (step m nodes (denseConstants m nodes)) titleLabels =
            .ok lastBefore ∧
          step m nodes (denseConstants m nodes) lastBefore n = .ok lastAfter ∧
          lastAfter[i]? ≠ lastBefore[i]? ∧
          IndexStableRun m nodes (denseConstants m nodes) i suffix lastAfter finalLabels) := by
  obtain ⟨nodes, titleLabels, finalLabels, hn, ht, hf, hts, hfs, hd⟩ :=
    public_label_execution m result h
  exact ⟨nodes, titleLabels, finalLabels, hn, ht, hts, hfs, hd,
    fold_last_index_change m nodes nodes (denseConstants m nodes)
      titleLabels finalLabels i hf⟩

def HeaderWriteRun (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel) : Prop :=
  let p := m.profile
  let cell := p == .cell
  let r := tileRect n.rect
  let name := before.findIdx? (fun l => l.source.id == n.source.id ++ ".name")
  let value := before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
  let nameText := ((name.bind fun j => before[j]?).map (·.source.text)).getD ""
  let valueText := ((value.bind fun j => before[j]?).map (·.source.text)).getD ""
  let ns := Int.fdiv (LayoutConst.treemap_header_label_size.get p) 64
  let vs := Int.fdiv (LayoutConst.treemap_header_value_size.get p) 64
  let lh := if cell then 1 else 1280
  let border := LayoutConst.treemap_header_border.get p
  let top := border + Int.fdiv (c.header - border - lh) 2
  let vi := LayoutConst.treemap_header_value_inset.get p
  let ni := LayoutConst.treemap_header_label_inset.get p
  ∃ vw fitted middle,
    (if value.isSome then width (fontFamily := m.options.fontFamily) cell valueText .body vs else pure 0) = .ok vw ∧
    let reserve := vi + vw + LayoutConst.treemap_header_gap.get p
    let showValue := value.isSome && decide (vw + vi + ni ≤ r.w) &&
      (name.isNone || decide (r.w - ni - reserve ≥ LayoutConst.treemap_header_label_min.get p))
    let avail := if showValue then r.w - ni - reserve else r.w - 2 * ni
    (match name with
      | none => fitted = none
      | some _ => fit (fontFamily := m.options.fontFamily) cell nameText avail .label ns = .ok fitted) ∧
    middle = (match name, fitted with
      | some j, some (shown, w) => before.modify j (fun l =>
        { putLabel l shown ⟨r.x + ni, r.y + top, w, lh⟩ ns with align := .start })
      | _, _ => before) ∧
    after = (if showValue then
      match value with
      | none => middle
      | some k => middle.modify k (fun l =>
        { putLabel l l.source.text ⟨r.x + r.w - vi - vw, r.y + top, vw, lh⟩ vs
          with align := .«end», italic := true })
      else middle)

theorem changed_header_write_run (m : Model) (c : Consts) (n : Node)
    (before after : List PlacedLabel)
    (h : placeHeader m c n before = .ok after) (hne : after ≠ before) :
    HeaderWriteRun m c n before after := by
  by_cases hh : (tileRect n.rect).h ≤
      LayoutConst.treemap_header_border.get m.profile +
        Int.fdiv (c.header - LayoutConst.treemap_header_border.get m.profile -
          (if m.profile == .cell then 1 else 1280)) 2 +
        (if m.profile == .cell then 1 else 1280)
  · exact False.elim (hne (Except.ok.inj
      (h.symm.trans (placeHeader_skip_height m c n before hh))))
  · cases hn : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") with
    | none =>
      obtain ⟨vw, hw, ho⟩ := placeHeader_absent_name_cases m c n before after hn hh h
      simp only [HeaderWriteRun, hn, Option.isNone_none, Bool.true_or, Bool.and_true]
      exact ⟨vw, none, before, hw, rfl, rfl, ho⟩
    | some j =>
      obtain ⟨vw, fitted, middle, hw, hf, hm, ho⟩ :=
        placeHeader_fit_cases m c n before after j hn hh h
      simp only [HeaderWriteRun, hn, Option.bind_some, Option.isNone_some, Bool.false_or]
      refine ⟨vw, fitted, middle, hw, hf, ?_, ho⟩
      cases fitted with
      | none => exact hm
      | some pair => cases pair; exact hm

def LeafWriteRun (m : Model) (lc : LeafConsts) (n : Node)
    (before after : List PlacedLabel) : Prop :=
  let cell := m.profile == .cell
  let r := tileRect n.rect
  let aw := r.w - 2 * lc.pad
  let ah := r.h - 2 * lc.pad
  let value := before.findIdx? (fun l => l.source.id == n.source.id ++ ".value")
  let valueText := ((value.bind fun k => before[k]?).map (·.source.text)).getD ""
  ∃ j ns shown nw vw middle,
    before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") = some j ∧
    (cell = true → ns = 0) ∧
    fit (fontFamily := m.options.fontFamily) cell (((before[j]?).map (·.source.text)).getD "") aw .label ns =
      .ok (some (shown, nw)) ∧
    let lh := if cell then 1 else 1280
    let vs := if cell then 0 else max (Int.fdiv lc.valueMin 64)
      (min (Int.fdiv lc.valueSize 64)
        (roundDiv (ns * LayoutConst.treemap_value_scale_percent.get m.profile) 100))
    let pair := 2 * lh + lc.spacing
    let room := decide (pair ≤ (if cell then ah else r.h))
    (if value.isSome && room then width (fontFamily := m.options.fontFamily) cell valueText .body vs else pure 0) = .ok vw ∧
    let showValue := value.isSome && room && decide (vw ≤ aw)
    let rows := if showValue then pair else lh
    let top := if cell then r.y + lc.pad + Int.fdiv (ah - rows) 2
      else r.y + Int.fdiv (r.h - rows) 2
    middle = before.modify j (fun l => putLabel l shown
      ⟨r.x + lc.pad + Int.fdiv (aw - nw) 2, top, nw, lh⟩ ns) ∧
    after = (if showValue then
      match value with
      | none => middle
      | some k => middle.modify k (fun l => putLabel l l.source.text
        ⟨r.x + lc.pad + Int.fdiv (aw - vw) 2, top + lh + lc.spacing, vw, lh⟩ vs)
      else middle)

theorem changed_leaf_write_run (m : Model) (lc : LeafConsts) (n : Node)
    (before after : List PlacedLabel)
    (h : placeLeaf m lc n before = .ok after) (hne : after ≠ before) :
    LeafWriteRun m lc n before after := by
  by_cases hd : (tileRect n.rect).w - 2 * lc.pad < lc.minDisplay ∨
      (tileRect n.rect).h - 2 * lc.pad < lc.minDisplay
  · exact False.elim (hne (Except.ok.inj
      (h.symm.trans (placeLeaf_skip_display m lc n before hd))))
  · cases hn : before.findIdx? (fun l => l.source.id == n.source.id ++ ".name") with
    | none =>
      exact False.elim (hne (Except.ok.inj
        (h.symm.trans (placeLeaf_skip_name m lc n before hn))))
    | some j =>
      cases hc : (m.profile == .cell) with
      | true =>
        rcases placeLeaf_cell_fit_cases m lc n before after j hc hn hd h with
          ⟨_, heq⟩ | ⟨shown, nw, vw, middle, hf, hw, hm, ho⟩
        · exact False.elim (hne heq)
        · refine ⟨j, 0, shown, nw, vw, middle, hn, ?_, ?_⟩
          · intro _; rfl
          · simpa only [hc, ↓reduceIte, Int.mul_one] using And.intro hf
              (And.intro hw (And.intro hm ho))
      | false =>
        obtain ⟨ns, cases⟩ := placeLeaf_vector_fit_cases m lc n before after j hc hn hd h
        rcases cases with ⟨_, heq⟩ | ⟨shown, nw, hf, cases⟩
        · exact False.elim (hne heq)
        · rcases cases with ⟨_, heq⟩ | ⟨vw, middle, _, hw, hm, ho⟩
          · exact False.elim (hne heq)
          · refine ⟨j, ns, shown, nw, vw, middle, hn, ?_, ?_⟩
            · simp only [hc, Bool.false_eq_true, false_implies]
            · simpa only [hc, Bool.false_eq_true, ↓reduceIte] using And.intro hf
                (And.intro hw (And.intro hm ho))

theorem title_origin_at_index (m : Model) (c : Consts) (after : List PlacedLabel)
    (h : placeTitle m c (initialLabels m) = .ok after) (i : Nat) :
    after[i]? = (initialLabels m)[i]? ∨
      ∃ l shown w,
        (initialLabels m).findIdx? (fun x => x.source.id == "title") = some i ∧
        (initialLabels m)[i]? = some l ∧
        fit (fontFamily := m.options.fontFamily) (m.profile == .cell) l.source.text c.width .title 16 = .ok (some (shown, w)) ∧
        after[i]? = some (putLabel l shown
          ⟨Int.fdiv (c.width - w) 2,
            Int.fdiv (c.titleBand - (if m.profile == .cell then 1 else 1536)) 2,
            w, if m.profile == .cell then 1 else 1536⟩ 16) := by
  rcases placeTitle_cases m c (initialLabels m) after h with heq |
    ⟨j, l, shown, w, hj, hl, hf, heq⟩
  · exact Or.inl (congrArg (fun ls : List PlacedLabel => ls[i]?) heq)
  · by_cases hi : j = i
    · subst j
      right
      refine ⟨l, shown, w, hj, hl, hf, ?_⟩
      rw [heq, modified_label_at_index]
      simp only [hl, ↓reduceIte, Option.map_some]
    · left
      rw [heq, modified_label_at_index]
      simp only [hi, ↓reduceIte]
      cases (initialLabels m)[i]? <;> rfl

theorem public_label_placement_cases (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) (i : Nat) :
    (result.scene.labels[i]?).map (fun l => (l.id, l.owner, l.text)) =
      (m.labels[i]?).map (fun l => (l.id, l.owner, l.text)) ∧
    ∃ nodes titleLabels finalLabels,
      tileNodes (constants m) (seededNodes m) = .ok nodes ∧
      result.scene.labels = finalLabels.map dumpLabel ∧
      ((finalLabels[i]? = titleLabels[i]? ∧
        placeTitle m (constants m) (initialLabels m) = .ok titleLabels ∧
        (titleLabels[i]? = (initialLabels m)[i]? ∨
          ∃ l shown w,
            (initialLabels m).findIdx? (fun x => x.source.id == "title") = some i ∧
            (initialLabels m)[i]? = some l ∧
            fit (fontFamily := m.options.fontFamily) (m.profile == .cell) l.source.text (constants m).width .title 16 =
              .ok (some (shown, w)) ∧
            titleLabels[i]? = some (putLabel l shown
              ⟨Int.fdiv ((constants m).width - w) 2,
                Int.fdiv ((constants m).titleBand - (if m.profile == .cell then 1 else 1536)) 2,
                w, if m.profile == .cell then 1 else 1536⟩ 16))) ∨
        ∃ prior n suffix lastBefore lastAfter,
          nodes = prior ++ n :: suffix ∧
          prior.foldlM (step m nodes (denseConstants m nodes)) titleLabels = .ok lastBefore ∧
          step m nodes (denseConstants m nodes) lastBefore n = .ok lastAfter ∧
          lastAfter[i]? ≠ lastBefore[i]? ∧
          sources lastBefore = m.labels ∧ sources lastAfter = m.labels ∧
          finalLabels[i]? = lastAfter[i]? ∧
          IndexStableRun m nodes (denseConstants m nodes) i suffix lastAfter finalLabels ∧
          ((n.source.id == "root") = false ∧
            (((children nodes n.source.id).isEmpty = true ∧
              LeafWriteRun m (denseConstants m nodes) n lastBefore lastAfter) ∨
             ((children nodes n.source.id).isEmpty = false ∧
              HeaderWriteRun m (constants m) n lastBefore lastAfter)))) := by
  refine ⟨public_label_identity_at_index m result h i, ?_⟩
  obtain ⟨nodes, titleLabels, finalLabels, hn, ht, hts, _, hd, cases⟩ :=
    public_last_label_placement m result h i
  refine ⟨nodes, titleLabels, finalLabels, hn, hd, ?_⟩
  rcases cases with stable | ⟨prior, n, suffix, lb, la, heq, hp, hs, hc, hr⟩
  · exact Or.inl ⟨stable.index_eq, ht,
      title_origin_at_index m (constants m) titleLabels ht i⟩
  · right
    have hbs := (fold_sources m nodes prior (denseConstants m nodes)
      titleLabels lb hp).trans hts
    have has := (step_sources m nodes (denseConstants m nodes) n lb la hs).trans hbs
    refine ⟨prior, n, suffix, lb, la, heq, hp, hs, hc, hbs, has, hr.index_eq, hr, ?_⟩
    have hne : la ≠ lb := fun he => hc (congrArg (fun ls : List PlacedLabel => ls[i]?) he)
    rcases step_cases m nodes (denseConstants m nodes) n lb la hs with
      ⟨_, he⟩ | ⟨hroot, hleaf, hl⟩ | ⟨hroot, hbranch, hh⟩
    · exact False.elim (hne he)
    · exact ⟨hroot, Or.inl ⟨hleaf,
        changed_leaf_write_run m (denseConstants m nodes) n lb la hl hne⟩⟩
    · exact ⟨hroot, Or.inr ⟨hbranch,
        changed_header_write_run m (constants m) n lb la hh hne⟩⟩

end Elegant.Treemap.LabelFacts
