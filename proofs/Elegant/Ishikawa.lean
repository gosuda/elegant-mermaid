theorem ishikawa_causes_alternate_next (i : Nat) :
    upper (i + 1) = !upper i := by
  have h := Nat.mod_lt i (by decide : 0 < 2)
  by_cases hi : i % 2 = 0
  · have hn : (i + 1) % 2 = 1 := by omega
    simp [upper, hi, hn]
  · have hi' : i % 2 = 1 := by omega
    have hn : (i + 1) % 2 = 0 := by omega
    simp [upper, hi', hn]

theorem extent_fold_left (pieces : List (Nat × Rect × List Point)) (initial : Int × Int)
    (piece : Nat × Rect × List Point) (hm : piece ∈ pieces) :
    (pieces.foldl (fun (l, right) v =>
      (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) initial).1 ≤ piece.2.1.x := by
  have shrink : ∀ (ps : List (Nat × Rect × List Point)) (st : Int × Int),
      (ps.foldl (fun (l, right) v =>
        (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) st).1 ≤ st.1 := by
    intro ps
    induction ps with
    | nil => intro st; exact Int.le_refl _
    | cons p ps ih =>
      intro st
      exact Int.le_trans (ih _) (Int.min_le_left _ _)
  induction pieces generalizing initial with
  | nil => simp at hm
  | cons p ps ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst piece
      exact Int.le_trans (shrink ps _) (Int.min_le_right _ _)
    · exact ih _ hm

theorem extent_piece_bounds (rs : List Rib) (piece : Nat × Rect × List Point)
    (hm : piece ∈ rs.flatMap (·.pieces)) :
    (extent rs).1 ≤ piece.2.1.x ∧
      piece.2.1.x + piece.2.1.w ≤ (extent rs).2 := by
  exact ⟨extent_fold_left _ _ _ hm, extent_fold_right _ _ _ hm⟩

theorem pair_slots_disjoint (earlier later : List Rib)
    (ceiling previous laterAttach : Int)
    (a b : Nat × Rect × List Point)
    (ha : a ∈ earlier.flatMap (·.pieces))
    (hb : b ∈ later.flatMap (·.pieces))
    (hprevious : previous = laterAttach + (extent later).1) :
    Disjoint
      { a.2.1 with x := a.2.1.x + min ceiling (previous - (extent earlier).2) }
      { b.2.1 with x := b.2.1.x + laterAttach } := by
  apply pair_boxes_disjoint
  · exact (extent_piece_bounds earlier a ha).2
  · have hleft := (extent_piece_bounds later b hb).1
    simp only
    omega

theorem depthBone_even_endpoints (p : Params) (par : Bone) (depth : Nat)
    (t count margin : Int) (h : depth % 2 = 0) :
    (depthBone p par depth t count margin).t0 = t ∧
      (depthBone p par depth t count margin).t1 = t ∧
      (depthBone p par depth t count margin).x1 =
        (depthBone p par depth t count margin).x0 - boneLength p count margin := by
  simp [depthBone, h]

theorem depthBone_odd_endpoints (p : Params) (par : Bone) (depth : Nat)
    (t count margin : Int) (h : depth % 2 ≠ 0) :
    (depthBone p par depth t count margin).t0 = par.t0 ∧
      (depthBone p par depth t count margin).t1 = t ∧
      (depthBone p par depth t count margin).x0 =
        par.x0 + Int.fdiv ((par.x1 - par.x0) * (par.count - par.drawn)) (par.count + 1) ∧
      (depthBone p par depth t count margin).x1 =
        (depthBone p par depth t count margin).x0 - run p (t - par.t0) := by
  have hodd : depth % 2 = 1 := by omega
  simp [depthBone, hodd]

theorem opposite_cause_slots_disjoint (spine upperLength lowerLength : Int)
    (upperX lowerX upperWidth lowerWidth upperHeight lowerHeight : Int)
    (hu : 0 ≤ upperLength) (hl : 0 ≤ lowerLength) :
    Disjoint
      ⟨upperX, ordinate spine true upperLength - upperHeight, upperWidth, upperHeight⟩
      ⟨lowerX, ordinate spine false lowerLength, lowerWidth, lowerHeight⟩ := by
  simp [Disjoint, Rect.meetsInterior, ordinate] <;> omega

theorem subcause_slots_disjoint (spine t₀ t₁ heightBound : Int) (up : Bool)
    (x₀ x₁ width₀ width₁ height₀ height₁ : Int)
    (h₀ : 0 ≤ height₀) (_h₁ : 0 ≤ height₁)
    (hb₀ : height₀ ≤ heightBound) (hb₁ : height₁ ≤ heightBound)
    (hgap : t₀ + heightBound ≤ t₁) :
    Disjoint
      ⟨x₀, ordinate spine up t₀ - Int.fdiv height₀ 2, width₀, height₀⟩
      ⟨x₁, ordinate spine up t₁ - Int.fdiv height₁ 2, width₁, height₁⟩ := by
  rw [Tree.fdiv2, Tree.fdiv2]
  cases up <;> simp [Disjoint, Rect.meetsInterior, ordinate] <;> omega
