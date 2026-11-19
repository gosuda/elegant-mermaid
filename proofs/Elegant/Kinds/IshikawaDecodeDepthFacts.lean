import Elegant.Kinds.Ishikawa
import Elegant.ForInFacts

set_option autoImplicit false

namespace Elegant.Kinds.Ishikawa

def DecodePathDepth (depths path : List Nat) : Prop :=
  ∀ (j index : Nat), path[j]? = some index → depths[index]? = some j

private theorem lookup_append_preserved {α : Type} (xs ys : List α)
    (i : Nat) (value : α) (h : xs[i]? = some value) :
    (xs ++ ys)[i]? = some value := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simpa using h
    | succ i =>
      simp only [List.getElem?_cons_succ] at h ⊢
      exact ih i h

private theorem lookup_take_origin {α : Type} (xs : List α)
    (count j : Nat) (value : α) (h : (xs.take count)[j]? = some value) :
    xs[j]? = some value ∧ j < count := by
  induction xs generalizing count j with
  | nil => simp at h
  | cons x xs ih =>
    cases count with
    | zero => simp at h
    | succ count =>
      cases j with
      | zero =>
        simp at h
        subst value
        simp
      | succ j =>
        simp only [List.take_succ_cons, List.getElem?_cons_succ] at h
        obtain ⟨hj, hlt⟩ := ih count j h
        exact ⟨by simpa using hj, by omega⟩

private theorem lookup_snoc_cases {α : Type} (xs : List α) (last : α)
    (j : Nat) (value : α) (h : (xs ++ [last])[j]? = some value) :
    xs[j]? = some value ∨ (j = xs.length ∧ value = last) := by
  induction xs generalizing j with
  | nil =>
    cases j with
    | zero => simp at h; exact Or.inr ⟨rfl, h.symm⟩
    | succ j => simp at h
  | cons x xs ih =>
    cases j with
    | zero => exact Or.inl (by simpa using h)
    | succ j =>
      simp only [List.cons_append, List.getElem?_cons_succ] at h
      rcases ih j h with hold | ⟨hj, hv⟩
      · exact Or.inl (by simpa using hold)
      · exact Or.inr ⟨by simpa using congrArg Nat.succ hj, hv⟩

theorem decodePathDepth_empty : DecodePathDepth [] [] := by
  intro j index h
  simp at h

theorem decodePathDepth_append (input : Input) (path : List Nat)
    (depth index : Nat) (halign : index = input.depths.length)
    (hpath : DecodePathDepth input.depths path) (hdepth : depth ≤ path.length) :
    DecodePathDepth (input.depths ++ [depth]) (path.take depth ++ [index]) := by
  intro j node hj
  rcases lookup_snoc_cases (path.take depth) index j node hj with hold | ⟨hposition, hn⟩
  · obtain ⟨horigin, _⟩ := lookup_take_origin path depth j node hold
    exact lookup_append_preserved input.depths [depth] node j (hpath j node horigin)
  · subst node
    have hlen : (path.take depth).length = depth := by
      simp [List.length_take, Nat.min_eq_left hdepth]
    have hjdepth : j = depth := hposition.trans hlen
    rw [hjdepth]
    subst index
    simp

theorem decode_append_alignment (input : Input) (parent : Option Nat)
    (width height depth : Nat) (halign : input.nodes.length = input.depths.length) :
    (input.nodes ++ [(⟨parent, width, height⟩ : Tree.Node)]).length =
      (input.depths ++ [depth]).length := by
  simp only [List.length_append, List.length_singleton]
  omega

theorem decode_parent_depth (input : Input) (path : List Nat)
    (depth parent : Nat) (hpath : DecodePathDepth input.depths path)
    (hpositive : 0 < depth)
    (hparent : (if depth == 0 then none else path[depth - 1]?) = some parent) :
    input.depths[parent]? = some (depth - 1) := by
  have hne : (depth == 0) = false := by simp; omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at hparent
  exact hpath (depth - 1) parent hparent

theorem decode_parent_successor (input : Input) (path : List Nat)
    (depth parent parentDepth : Nat) (hpath : DecodePathDepth input.depths path)
    (hpositive : 0 < depth)
    (hparent : (if depth == 0 then none else path[depth - 1]?) = some parent)
    (hlookup : input.depths[parent]? = some parentDepth) :
    depth = parentDepth + 1 := by
  have hp := decode_parent_depth input path depth parent hpath hpositive hparent
  rw [hlookup] at hp
  have heq := Option.some.inj hp
  omega

theorem decode_empty_cell (m : Model) (hprofile : m.profile = .cell)
    (hboxes : m.boxes = []) : decode m = .ok ({} : Input) := by
  simp [decode, hprofile, hboxes, Common.labelMetric, pure, Except.pure,
    bind, Except.bind]

theorem decode_first_root_lookup (input : Input) (hempty : input.depths = []) :
    (input.depths ++ [0])[0]? = some 0 := by
  simp [hempty]

theorem decode_path_index_bound (input : Input) (path : List Nat)
    (halign : input.nodes.length = input.depths.length)
    (hpath : DecodePathDepth input.depths path)
    (j index : Nat) (hlookup : path[j]? = some index) :
    index < input.nodes.length := by
  have hbound := (List.getElem?_eq_some_iff.mp (hpath j index hlookup)).1
  omega

def DecodeParentDepth (nodes : List Tree.Node) (depths : List Nat) : Prop :=
  ∀ (i : Nat) (node : Tree.Node), nodes[i]? = some node →
    ∀ parent, node.parent = some parent →
      ∃ depth, depths[parent]? = some depth ∧ depths[i]? = some (depth + 1)

theorem decodeParentDepth_empty : DecodeParentDepth [] [] := by
  intro i node hnode
  simp at hnode

theorem decodeParentDepth_append (input : Input) (path : List Nat)
    (depth width height : Nat)
    (halign : input.nodes.length = input.depths.length)
    (hpath : DecodePathDepth input.depths path)
    (hparents : DecodeParentDepth input.nodes input.depths) :
    DecodeParentDepth
      (input.nodes ++ [(⟨if depth == 0 then none else path[depth - 1]?,
        width, height⟩ : Tree.Node)])
      (input.depths ++ [depth]) := by
  intro i node hnode parent hparent
  rcases lookup_snoc_cases input.nodes
      (⟨if depth == 0 then none else path[depth - 1]?, width, height⟩ : Tree.Node)
      i node hnode with hold | ⟨hposition, hnew⟩
  · obtain ⟨stored, hp, hi⟩ := hparents i node hold parent hparent
    exact ⟨stored,
      lookup_append_preserved input.depths [depth] parent stored hp,
      lookup_append_preserved input.depths [depth] i (stored + 1) hi⟩
  · subst node
    have hpositive : 0 < depth := by
      by_cases hz : depth = 0
      · simp [hz] at hparent
      · omega
    have hp := decode_parent_depth input path depth parent hpath hpositive hparent
    refine ⟨depth - 1,
      lookup_append_preserved input.depths [depth] parent (depth - 1) hp, ?_⟩
    rw [hposition, halign]
    have hsucc : depth - 1 + 1 = depth := by omega
    simp [hsucc]

theorem decodeParentDepth_children (nodes : List Tree.Node) (depths : List Nat)
    (hparents : DecodeParentDepth nodes depths)
    (parent depth : Nat) (hdepth : depths[parent]? = some depth)
    (i : Nat) (hchild : i ∈ Elegant.Ishikawa.children nodes parent) :
    depths[i]? = some (depth + 1) := by
  unfold Elegant.Ishikawa.children at hchild
  have hp := (List.mem_filter.mp hchild).2
  cases hn : nodes[i]? with
  | none => simp [hn] at hp
  | some node =>
    have hparent : node.parent = some parent := by simpa [hn] using hp
    obtain ⟨stored, hs, hi⟩ := hparents i node hn parent hparent
    rw [hdepth] at hs
    have heq : depth = stored := Option.some.inj hs
    simpa [heq] using hi

structure DecodeDepthState (input : Input) (path : List Nat) : Prop where
  aligned : input.nodes.length = input.depths.length
  pathLength : path.length ≤ input.depths.length
  pathDepth : DecodePathDepth input.depths path
  parentDepth : DecodeParentDepth input.nodes input.depths
  root : input.depths = [] ∨ input.depths[0]? = some 0

theorem decodeDepthState_empty : DecodeDepthState ({} : Input) [] := by
  exact ⟨rfl, Nat.le_refl 0, decodePathDepth_empty, decodeParentDepth_empty, Or.inl rfl⟩

theorem decodeDepthState_append (input : Input) (path : List Nat)
    (depth index width height : Nat) (lines : List Measure.Line) (text : String)
    (hstate : DecodeDepthState input path) (hindex : index = input.nodes.length)
    (hdepth : depth ≤ path.length) :
    DecodeDepthState
      { nodes := input.nodes ++
          [(⟨if depth == 0 then none else path[depth - 1]?, width, height⟩ : Tree.Node)]
        depths := input.depths ++ [depth]
        lines := input.lines ++ [lines]
        source := input.source ++ [text] }
      (path.take depth ++ [index]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact decode_append_alignment input _ width height depth hstate.aligned
  · simp only [List.length_append, List.length_singleton, List.length_take]
    have hmin : min depth path.length ≤ depth := Nat.min_le_left _ _
    have hlength := hstate.pathLength
    omega
  · exact decodePathDepth_append input path depth index
      (hindex.trans hstate.aligned) hstate.pathDepth hdepth
  · exact decodeParentDepth_append input path depth width height
      hstate.aligned hstate.pathDepth hstate.parentDepth
  · right
    rcases hstate.root with hempty | hroot
    · have hlength := hstate.pathLength
      rw [hempty] at hlength
      have hzero : depth = 0 := by simp only [List.length_nil] at hlength; omega
      simp [hempty, hzero]
    · exact lookup_append_preserved input.depths [depth] 0 0 hroot

theorem decodeDepthState_nonempty_root (input : Input) (path : List Nat)
    (hstate : DecodeDepthState input path) (hnonempty : input.nodes ≠ []) :
    input.depths[0]? = some 0 := by
  rcases hstate.root with hempty | hroot
  · have halign := hstate.aligned
    rw [hempty] at halign
    have hnodes : input.nodes = [] := List.length_eq_zero_iff.mp halign
    exact False.elim (hnonempty hnodes)
  · exact hroot

private theorem decode_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem decode_ok_bind {α β : Type} (a : α)
    (f : α → Except LayoutError β) :
    ((pure a : Except LayoutError α) >>= f) = f a := rfl

private theorem decode_processed_index (boxes : List ModelBox)
    (done rest : List (ModelBox × Nat)) (box : ModelBox) (index : Nat)
    (hprefix : boxes.zipIdx = done ++ (box, index) :: rest) :
    index = done.length := by
  have hlookup : boxes.zipIdx[done.length]? = some (box, index) := by
    rw [hprefix]
    simp
  rw [List.getElem?_zipIdx] at hlookup
  cases hb : boxes[done.length]? with
  | none => simp [hb] at hlookup
  | some b =>
    simp [hb] at hlookup
    exact hlookup.2.symm

private theorem decodeDepthState_append_measured (input : Input) (path : List Nat)
    (depth index : Nat) (width height : Int) (lines : List Measure.Line) (text : String)
    (hstate : DecodeDepthState input path) (hindex : index = input.nodes.length)
    (hdepth : depth ≤ path.length) :
    DecodeDepthState
      { nodes := input.nodes ++
          [(⟨if depth == 0 then none else path[depth - 1]?,
            max width 1, max height 1⟩ : Tree.Node)]
        depths := input.depths ++ [depth]
        lines := input.lines ++ [lines]
        source := input.source ++ [text] }
      (path.take depth ++ [index]) := by
  have hw : 0 ≤ max width 1 := by omega
  have hh : 0 ≤ max height 1 := by omega
  have h := decodeDepthState_append input path depth index
    (max width 1).toNat (max height 1).toNat lines text hstate hindex hdepth
  simpa only [Int.toNat_of_nonneg hw, Int.toNat_of_nonneg hh] using h

theorem successful_decode_depth_state {m : Model} {input : Input}
    (hdecode : decode m = .ok input) : ∃ path, DecodeDepthState input path := by
  unfold decode at hdecode
  obtain ⟨metric, _, hdecode⟩ := decode_bind_ok hdecode
  obtain ⟨output, hrun, hreturn⟩ := decode_bind_ok hdecode
  have hstate :
      DecodeDepthState output.1 output.2.1 ∧
        (output.2.2 = false → output.1.nodes.length = m.boxes.zipIdx.length) := by
    apply Elegant.forIn_processed [] m.boxes.zipIdx _ output _
      (fun done state =>
        DecodeDepthState state.1 state.2.1 ∧
          (state.2.2 = false → state.1.nodes.length = done.length))
      ⟨decodeDepthState_empty, by simp⟩ _ hrun
    intro done entry rest state next hprefix hstate hstep
    rcases entry with ⟨box, index⟩
    have hindex := decode_processed_index m.boxes done rest box index (by simpa using hprefix)
    dsimp only at hstep
    by_cases hanchor : (box.shape == "anchor") = true
    · simp only [hanchor, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hstep
      subst next
      exact ⟨_, rfl, hstate.1, by simp⟩
    · simp only [hanchor] at hstep
      by_cases hended : state.2.2 = true
      · simp only [hended, ↓reduceIte, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hstep
        cases hstep
      · have hfalse : state.2.2 = false := by
          cases hb : state.2.2 with
          | false => rfl
          | true => exact False.elim (hended hb)
        simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hstep
        split at hstep
        rotate_left
        split at hstep
        rotate_left
        simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
        cases hstep
        rotate_left
        split at hstep
        rotate_left
        simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
        cases hstep
        rotate_left
        split at hstep
        rotate_left
        simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
        cases hstep
        all_goals
          simp only [decode_ok_bind] at hstep
          split at hstep
          · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
            cases hstep
          · rename_i hdepth
            obtain ⟨lines, _, hstep⟩ := decode_bind_ok hstep
            split at hstep <;>
              (split at hstep
               · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
                 cases hstep
               · simp only [pure, Except.pure, Except.ok.injEq] at hstep
                 subst next
                 refine ⟨_, rfl, ?_, ?_⟩
                 · apply decodeDepthState_append_measured
                   · exact hstate.1
                   · exact hindex.trans (hstate.2 hfalse).symm
                   · omega
                 · intro _
                   simp only [List.length_append, List.length_singleton]
                   have hlength := hstate.2 hfalse
                   omega)
  simp only [pure, Except.pure, Except.ok.injEq] at hreturn
  exact ⟨output.2.1, hreturn ▸ hstate.1⟩

theorem successful_decode_root_depth {m : Model} {input : Input}
    (hdecode : decode m = .ok input) (hnonempty : input.nodes ≠ []) :
    input.depths[0]? = some 0 := by
  obtain ⟨path, hstate⟩ := successful_decode_depth_state hdecode
  exact decodeDepthState_nonempty_root input path hstate hnonempty

theorem successful_decode_child_depth {m : Model} {input : Input}
    (hdecode : decode m = .ok input) (parent depth : Nat)
    (hdepth : input.depths[parent]? = some depth) (i : Nat)
    (hchild : i ∈ Elegant.Ishikawa.children input.nodes parent) :
    input.depths[i]? = some (depth + 1) := by
  obtain ⟨path, hstate⟩ := successful_decode_depth_state hdecode
  exact decodeParentDepth_children input.nodes input.depths hstate.parentDepth
    parent depth hdepth i hchild

end Elegant.Kinds.Ishikawa
