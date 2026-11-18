import Elegant.Kinds.Ishikawa
import Elegant.TreeNormalized
import Elegant.TreeFacts
import Elegant.Kinds.GitgraphFacts
import Elegant.ForInFacts

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaValid

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem forIn_preserves {α β : Type} (xs : List α)
    (step : α → β → Except LayoutError (ForInStep β)) (invariant : β → Prop)
    (initial final : β) (hinit : invariant initial)
    (hstep : ∀ a ∈ xs, ∀ state next, invariant state →
      step a state = .ok next → invariant next.value)
    (hrun : forIn xs initial step = .ok final) : invariant final := by
  induction xs generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hrun
    subst final
    exact hinit
  | cons a xs ih =>
    rw [List.forIn_cons] at hrun
    cases hs : step a initial with
    | error err => simp [hs, bind, Except.bind] at hrun
    | ok next =>
      have hn := hstep a (List.mem_cons_self ..) initial next hinit hs
      cases next with
      | done state =>
        simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hrun
        subst final
        exact hn
      | yield state =>
        simp only [hs, bind, Except.bind] at hrun
        exact ih state hn (fun b hb => hstep b (List.mem_cons_of_mem a hb)) hrun

private theorem set_isEmpty_false (l : List Rect) (i : Nat) (a : Rect)
    (h : l.isEmpty = false) : (l.set i a).isEmpty = false := by
  cases l with
  | nil => cases h
  | cons hd tl =>
    cases i with
    | zero => rfl
    | succ n => rfl

private theorem drop_one_le {α : Type} (l : List α) : (l.drop 1).length ≤ l.length := by
  cases l with
  | nil => simp
  | cons hd tl => simp

theorem layout_empty_nodes (p : Elegant.Ishikawa.Params) (raw : Elegant.Tree.Layout)
    (h : Elegant.Ishikawa.layout [] p = .ok raw) : raw = (⟨[], []⟩ : Elegant.Tree.Layout) := by
  have h2 : Elegant.Ishikawa.layout [] p = .ok (⟨[], []⟩ : Elegant.Tree.Layout) := by
    simp [Elegant.Ishikawa.layout, List.isEmpty, Pure.pure, Except.pure]
  have heq := h2.symm.trans h
  exact (Except.ok.inj heq).symm

theorem raw_hraw_empty (ns : List Elegant.Tree.Node) (p : Elegant.Ishikawa.Params)
    (raw : Elegant.Tree.Layout) (hempty : ns = [])
    (h : Elegant.Ishikawa.layout ns p = .ok raw) :
    ∀ pts ∈ raw.routes, pts ≠ [] → raw.boxes.isEmpty = false := by
  subst hempty
  have hraw := layout_empty_nodes p raw h
  intro pts hmem hne
  rw [hraw] at hmem
  dsimp at hmem
  simp at hmem

private theorem initial_isEmpty_false (ns : List Elegant.Tree.Node) (hne : ns ≠ [])
    (spine : Int) (head : Elegant.Tree.Node) :
    (((List.replicate ns.length (⟨0, 0, 0, 0⟩ : Rect)).set 0
      ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩).isEmpty = false) := by
  cases ns with
  | nil => cases hne rfl
  | cons hd tl => rfl

private theorem assemblePairs_isEmpty_aux (spine : Int) (n : Nat) :
    ∀ (rs : List Elegant.Ishikawa.Rib) (ceiling previous : Int) (out out' : Elegant.Tree.Layout),
    rs.length ≤ n →
    out.boxes.isEmpty = false →
    Elegant.Ishikawa.assemblePairs spine rs ceiling previous out = .ok out' →
    out'.boxes.isEmpty = false := by
  induction n with
  | zero =>
    intro rs ceiling previous out out' hlen hinv h
    cases rs with
    | nil =>
      simp only [Elegant.Ishikawa.assemblePairs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst out'
      exact hinv
    | cons a rest =>
      simp only [List.length_cons] at hlen
      omega
  | succ n ih =>
    intro rs ceiling previous out out' hlen hinv h
    cases rs with
    | nil =>
      simp only [Elegant.Ishikawa.assemblePairs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst out'
      exact hinv
    | cons a rest =>
      simp only [Elegant.Ishikawa.assemblePairs] at h
      obtain ⟨mid, hloop, htail⟩ := bind_ok h
      have hmid : mid.boxes.isEmpty = false := by
        apply forIn_preserves _ _ (fun s => s.boxes.isEmpty = false) _ _ hinv _ hloop
        intro r _hr s sn hsInv hstep
        obtain ⟨innerOut, hinner, hyield⟩ := bind_ok hstep
        have hinnerInv : innerOut.boxes.isEmpty = false := by
          apply forIn_preserves _ _ (fun s => s.boxes.isEmpty = false) _ _ hsInv _ hinner
          intro p _hp s2 s3 hs2 h3
          split at h3
          · cases h3
          · simp only [pure, Except.pure, Except.ok.injEq] at h3
            subst s3
            exact set_isEmpty_false _ _ _ hs2
        cases sn with
        | done s => cases hyield
        | yield s =>
          cases hyield
          exact hinnerInv
      have hrest : rest.length ≤ n := by
        simp only [List.length_cons] at hlen
        omega
      have hdrop : (rest.drop 1).length ≤ n :=
        Nat.le_trans (drop_one_le rest) hrest
      apply ih _ _ _ _ _ hdrop ?_ htail
      exact hmid

theorem raw_boxes_nonempty (ns : List Elegant.Tree.Node) (p : Elegant.Ishikawa.Params)
    (raw : Elegant.Tree.Layout) (hne : ns ≠ [])
    (h : Elegant.Ishikawa.layout ns p = .ok raw) : raw.boxes.isEmpty = false := by
  cases ns with
  | nil => cases hne rfl
  | cons hd tl =>
    unfold Elegant.Ishikawa.layout at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hlink : ((!Tree.link (hd :: tl)) || ((hd :: tl).any fun n => n.width < 1 || n.height < 1)) = true
    · rw [ite_eq_left hlink] at h
      simp only [bind, Except.bind] at h
      cases h
    · rw [ite_eq_right hlink] at h
      by_cases hparams : (p.spineBase < 5 || p.ribMin < 5 || p.ribPool < 1 || p.spacing < 1 || p.stub < 1 || p.base < 1 || p.perChild < 0 || p.inset < 0 || p.cos < 0 || p.sin < 1) = true
      · rw [ite_eq_left hparams] at h
        simp only [bind, Except.bind] at h
        cases h
      · rw [ite_eq_right hparams] at h
        obtain ⟨_, _, h2⟩ := bind_ok h
        dsimp at h2
        obtain ⟨_, _, h3⟩ := bind_ok h2
        simp only [List.getElem?_cons_zero] at h3
        have hne' : (hd :: tl) ≠ [] := by simp
        apply assemblePairs_isEmpty_aux _ _ _ _ _ _ _ (Nat.le_refl _) ?_ h3
        exact initial_isEmpty_false (hd :: tl) hne' _ hd

theorem raw_hraw_full (m : Model) :
    ∀ (input : Elegant.Kinds.Ishikawa.Input) (raw : Elegant.Tree.Layout),
    Elegant.Kinds.Ishikawa.decode m = .ok input →
    Elegant.Ishikawa.layout input.nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw →
    ∀ pts ∈ raw.routes, pts ≠ [] → raw.boxes.isEmpty = false := by
  intro input raw _hdec hlay pts hmem hne
  cases hnodes : input.nodes with
  | nil => exact raw_hraw_empty _ _ _ hnodes hlay pts hmem hne
  | cons hd tl =>
    have hne' : input.nodes ≠ [] := by simp [hnodes]
    exact raw_boxes_nonempty _ _ _ hne' hlay

theorem ishikawa_c1 (m : Model) (result : Layered.FamilyResult)
    (_wf : WellFormed m) (_limits : WithinLimits m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C1 result.scene.layoutDump :=
  Elegant.Kinds.Ishikawa.ishikawa_c1_of_raw_nonempty m result (raw_hraw_full m) h

theorem ishikawa_c4_of_placed (m : Model) (result : Layered.FamilyResult)
    (_wf : WellFormed m) (_limits : WithinLimits m)
    (hplaced_orth : ∀ (input : Elegant.Kinds.Ishikawa.Input) (canvas : Size) (placed : Elegant.Tree.Layout),
      Elegant.Kinds.Ishikawa.decode m = .ok input →
      (∃ raw : Elegant.Tree.Layout,
        Elegant.Ishikawa.layout input.nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw ∧
        Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw = .ok (canvas, placed)) →
      ∀ (k : Nat) (depth : Nat) (pts : List Point),
      input.depths[k]? = some depth → placed.routes[k]? = some pts →
      depth % 2 = 0 → Polyline.isOrthogonal pts = true)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C4 result.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := Elegant.Kinds.Ishikawa.layout_success_scene m result h
  rw [hd]
  intro r hr horth
  unfold Elegant.Kinds.Ishikawa.scene at hs
  obtain ⟨input, hinput, hs⟩ := bind_ok hs
  obtain ⟨raw, hrawok, hs⟩ := bind_ok hs
  obtain ⟨pair, hpair, hs⟩ := bind_ok hs
  obtain ⟨canvas, placed⟩ := pair
  obtain ⟨boxes0, _, hs⟩ := bind_ok hs
  dsimp at hs
  obtain ⟨triple, hloop, hrest⟩ := bind_ok hs
  have htriple : ∀ r ∈ triple.2.1, r.orthogonal = true → Polyline.isOrthogonal r.points = true := by
    apply forIn_preserves _ _ (fun st => ∀ r ∈ st.2.1, r.orthogonal = true → Polyline.isOrthogonal r.points = true) _ _ _ _ hloop
    · intro r hr _hflag
      simp at hr
    · intro entry _hr st sn hsInv hstep
      cases hfind : (m.boxes.take input.nodes.length).findIdx? (·.id == entry.1.toId) with
      | none => simp only [hfind, bind, Except.bind] at hstep; cases hstep
      | some k =>
        cases hdepth : input.depths[k]? with
        | none => simp only [hfind, hdepth, bind, Except.bind] at hstep; cases hstep
        | some depth =>
          by_cases hguard : (!Elegant.Kinds.Ishikawa.consistentOrthogonal depth entry.1.orthogonal) = true
          · simp only [hfind, hdepth, hguard, bind, Except.bind, ite_true] at hstep
            cases hstep
          · cases hanchor : st.1[input.nodes.length + entry.2]? with
            | none =>
              simp only [hfind, hdepth, hguard, hanchor, bind, Except.bind] at hstep
              cases hstep
            | some anchor =>
              cases hpoints : placed.routes[k]? with
              | none =>
                simp only [hfind, hdepth, hguard, hanchor, hpoints, bind, Except.bind] at hstep
                cases hstep
              | some points =>
                cases hpts : points with
                | nil =>
                  simp only [hfind, hdepth, hguard, hanchor, hpoints, hpts, bind, Except.bind] at hstep
                  cases hstep
                | cons a tail =>
                  cases tail with
                  | nil =>
                    simp only [hfind, hdepth, hguard, hanchor, hpoints, hpts, bind, Except.bind] at hstep
                    cases hstep
                  | cons b rest =>
                    by_cases hid : (anchor.id != entry.1.fromId) = true
                    · simp only [hfind, hdepth, hguard, hanchor, hpoints, hpts, hid, bind, Except.bind, ite_true] at hstep
                      cases hstep
                    · simp only [hfind, hdepth, hguard, hanchor, hpoints, hpts, hid, bind, Except.bind, pure, Except.pure] at hstep
                      cases hstep
                      intro q hq hqorth
                      simp only [ForInStep.value, List.mem_append, List.mem_singleton] at hq
                      rcases hq with hq | rfl
                      · exact hsInv q hq hqorth
                      · have heven := Elegant.Kinds.Ishikawa.accepted_orthogonal_depth depth entry.1.orthogonal hguard hqorth
                        simpa only [hpts] using hplaced_orth input canvas placed hinput
                          ⟨raw, hrawok, hpair⟩ k depth points hdepth hpoints heven
  obtain ⟨_, _, hret⟩ := bind_ok hrest
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
  subst s
  exact htriple r hr horth

theorem ishikawa_c8b (m : Model) (result : Layered.FamilyResult)
    (_wf : WellFormed m) (_limits : WithinLimits m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C8b result.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := Elegant.Kinds.Ishikawa.layout_success_scene m result h
  rw [hd]
  have labels := Elegant.Kinds.Ishikawa.scene_labels_empty m s hs
  simp [Validator.C8b, Scene.layoutDump, labels]

theorem ishikawa_proved_clauses (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C1 result.scene.layoutDump ∧ Validator.C3 result.scene.layoutDump ∧
    Validator.C7 result.scene.layoutDump ∧ Validator.C8b result.scene.layoutDump :=
  ⟨ishikawa_c1 m result hwf hlim h,
   Elegant.Kinds.Ishikawa.ishikawa_c3 m result hwf hlim h,
   Elegant.Kinds.Ishikawa.ishikawa_c7 m result hwf hlim h,
   ishikawa_c8b m result hwf hlim h⟩

private theorem le_fdiv_of_mul_le {t D a : Int} (hD : 0 < D)
    (h : D * a ≤ t) : a ≤ Int.fdiv t D := by
  have hhi := Int.lt_fdiv_add_one_mul_self t hD
  by_cases hle : a ≤ Int.fdiv t D
  · exact hle
  · have hle' : Int.fdiv t D + 1 ≤ a := by omega
    have h2 := Int.mul_le_mul_of_nonneg_left hle' (Int.le_of_lt hD)
    rw [Int.mul_add, Int.mul_one] at h2
    rw [Int.add_mul, Int.one_mul, Int.mul_comm (Int.fdiv t D) D] at hhi
    omega

private theorem fdiv_le_of_le_mul {t D b : Int} (hD : 0 < D)
    (h : t ≤ D * b) : Int.fdiv t D ≤ b := by
  have hq := Int.mul_fdiv_add_fmod t D
  have hlo := Int.fmod_nonneg_of_pos t hD
  exact Int.le_of_mul_le_mul_left (by omega) hD

private theorem t_gap {L N H p1 p2 t1 t2 : Int}
    (hN : 0 < N) (hL : 0 ≤ L)
    (hLH : N * H ≤ L) (hlt : p1 < p2)
    (ht1 : t1 = Int.fdiv (L * p1) N) (ht2 : t2 = Int.fdiv (L * p2) N) :
    t1 + H ≤ t2 := by
  have hq1 := Int.mul_fdiv_add_fmod (L * p1) N
  have hm1 := Int.fmod_nonneg_of_pos (L * p1) hN
  have hNt1 : N * t1 ≤ L * p1 := by
    rw [ht1]
    omega
  have hpd : 1 ≤ p2 - p1 := by omega
  have hLd := Int.mul_le_mul_of_nonneg_left hpd hL
  rw [Int.mul_one] at hLd
  have hNHL : N * H ≤ L * (p2 - p1) := Int.le_trans hLH hLd
  have heq : L * p1 + L * (p2 - p1) = L * p2 := by
    rw [Int.mul_sub]
    omega
  have hLp1 : L * p1 + N * H ≤ L * p2 := by omega
  have hNth : N * (t1 + H) ≤ L * p2 := by
    rw [Int.mul_add]
    omega
  have hle := le_fdiv_of_mul_le hN hNth
  rw [← ht2] at hle
  exact hle

private theorem disjoint_of_zero_left {a b : Rect}
    (h : a.w ≤ 0 ∨ a.h ≤ 0 ∨ b.w ≤ 0 ∨ b.h ≤ 0) :
    Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, hy⟩
  rcases h with hw | hh | hw' | hh' <;> omega



/-! ### C5 route-endpoint boundary infrastructure

The validator's C5 requires every emitted route endpoint to land on the
boundary of the corresponding box.  At the raw level, `place` emits for each
entry a two-point route `⟨b.x0, ord b.t0⟩ → ⟨b.x1, ey⟩` whose last point
`⟨b.x1, ey⟩` is the left edge of that entry's subcause box, and `assemblePairs`
only translates every piece by a common x offset.  The lemmas below package
the per-piece boundary fact and the x-translation invariance needed to carry
it through `assemblePairs` and normalisation.
-/

private theorem onBoundary_shift_x {p : Point} {r : Rect} (d : Int)
    (h : Validator.onBoundary p r) :
    Validator.onBoundary ⟨p.x + d, p.y⟩ ⟨r.x + d, r.y, r.w, r.h⟩ := by
  unfold Validator.onBoundary at h ⊢
  dsimp only
  omega

/-- The boundary guarantee for one entry piece produced by `Ishikawa.place`:
its route is the two-point list `⟨b.x0, ord b.t0⟩ → ⟨b.x1, ey⟩`, whose last
point `⟨b.x1, ey⟩` lies on the right edge of the subcause box. -/
private theorem entry_piece_boundary {ns : List Elegant.Tree.Node}
    (p : Elegant.Ishikawa.Params) (spine : Int) (par : Elegant.Ishikawa.Bone)
    (e : Elegant.Ishikawa.Entry) (pos : Nat × Nat) (r : Elegant.Ishikawa.Rib)
    (n : Elegant.Tree.Node) (hw : 0 ≤ n.width) (hh : 0 ≤ n.height) :
    let b := Elegant.Ishikawa.depthBone p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        ((Elegant.Ishikawa.children ns e.node).length : Int)
        (Elegant.Ishikawa.run p r.heights + 3)
    let ey := Elegant.Ishikawa.ordinate spine r.upper b.t1
    Validator.onBoundary ⟨b.x1, ey⟩
      ⟨b.x1 - n.width, ey - Int.fdiv n.height 2, n.width, n.height⟩ := by
  dsimp only
  exact Elegant.Kinds.Ishikawa.subcause_endpoint_boundary _ spine r.upper
    n.width n.height hw hh

/-- Route-level packaging of `entry_piece_boundary`: the appended entry piece's
two-point route has its last point on its own rect boundary. -/
private theorem entry_piece_route_boundary {ns : List Elegant.Tree.Node}
    (p : Elegant.Ishikawa.Params) (spine : Int) (par : Elegant.Ishikawa.Bone)
    (e : Elegant.Ishikawa.Entry) (pos : Nat × Nat) (r : Elegant.Ishikawa.Rib)
    (n : Elegant.Tree.Node) (hw : 0 ≤ n.width) (hh : 0 ≤ n.height) :
    let b := Elegant.Ishikawa.depthBone p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        ((Elegant.Ishikawa.children ns e.node).length : Int)
        (Elegant.Ishikawa.run p r.heights + 3)
    let ey := Elegant.Ishikawa.ordinate spine r.upper b.t1
    ∃ q, [⟨b.x0, Elegant.Ishikawa.ordinate spine r.upper b.t0⟩, ⟨b.x1, ey⟩].getLast? =
        some q ∧
      Validator.onBoundary q
        ⟨b.x1 - n.width, ey - Int.fdiv n.height 2, n.width, n.height⟩ := by
  dsimp only
  let b := Elegant.Ishikawa.depthBone p par e.depth
      (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      ((Elegant.Ishikawa.children ns e.node).length : Int)
      (Elegant.Ishikawa.run p r.heights + 3)
  let ey := Elegant.Ishikawa.ordinate spine r.upper b.t1
  refine ⟨⟨b.x1, ey⟩, ?_, ?_⟩
  · rfl
  · exact Elegant.Kinds.Ishikawa.subcause_endpoint_boundary b spine r.upper
      n.width n.height hw hh

/-- Every piece emitted by a successful `Ishikawa.place` has a nonempty route
whose last point lies on that piece's own rect boundary.  The cause piece is
discharged by `cause_endpoint_boundary`; each appended entry piece by
`entry_piece_route_boundary`. -/
private theorem place_pieces_boundary (ns : List Elegant.Tree.Node)
    (hdims : ∀ n ∈ ns, 0 ≤ n.width ∧ 0 ≤ n.height)
    (p : Elegant.Ishikawa.Params) (spine : Int) (r r' : Elegant.Ishikawa.Rib)
    (h : Elegant.Ishikawa.place ns p spine r = .ok r') :
    ∀ i rect pts, (i, rect, pts) ∈ r'.pieces →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect := by
  simp only [Elegant.Ishikawa.place] at h
  cases hcause : ns[r.cause]? with
  | none => simp only [hcause] at h; cases h
  | some hc =>
    obtain ⟨hcW, hcH⟩ := hdims hc (List.mem_of_getElem? hcause)
    simp only [hcause] at h
    obtain ⟨mid, hloop, hret⟩ := bind_ok h
    have hr' : r' = { r with pieces := mid.1 } := by
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
      exact hret.symm
    have hinv : ∀ i rect pts, (i, rect, pts) ∈ mid.1 →
        ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect := by
      apply forIn_preserves _ _ (fun st =>
        ∀ i rect pts, (i, rect, pts) ∈ st.1 →
          ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect) _ _ ?_ _ hloop
      · intro i rect pts hmem
        simp at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        refine ⟨⟨-Elegant.Ishikawa.run p r.length,
          Elegant.Ishikawa.ordinate spine r.upper r.length⟩, ?_, ?_⟩
        · simp
        · exact Elegant.Kinds.Ishikawa.cause_endpoint_boundary _ _ _ _ _ hcW hcH
      · intro a _ha state next hi hstep
        obtain ⟨e, idx⟩ := a
        cases hpar : state.2[(e.parent + 1).toNat]? with
        | none => simp only [hpar, bind, Except.bind] at hstep; cases hstep
        | some par =>
          cases hpos : (r.order.zipIdx.find? (fun v => v.1 == idx)) with
          | none => simp only [hpar, hpos, bind, Except.bind] at hstep; cases hstep
          | some pos =>
            by_cases hg : ((e.depth % 2 == 0) &&
                decide (par.t1 ≤ par.t0)) = true
            · simp only [hpar, hpos, hg, ite_true, bind, Except.bind] at hstep
              cases hstep
            · simp only [hpar, hpos, hg, Bool.false_eq_true, ↓reduceIte,
                bind, Except.bind] at hstep
              split at hstep
              all_goals
                cases hn : ns[e.node]? with
                | none =>
                  simp only [hn] at hstep
                  cases hstep
                | some n =>
                  obtain ⟨nW, nH⟩ := hdims n (List.mem_of_getElem? hn)
                  simp only [hn, pure, Except.pure, Except.ok.injEq] at hstep
                  subst next
                  intro i rect pts hmem
                  simp only [ForInStep.value, List.mem_append,
                    List.mem_singleton, Prod.mk.injEq] at hmem
                  rcases hmem with hmem | ⟨rfl, rfl, rfl⟩
                  · exact hi i rect pts hmem
                  · exact entry_piece_route_boundary (ns := ns) p spine par e pos r n nW nH
    subst r'
    intro i rect pts hmem
    exact hinv i rect pts hmem

theorem placed_piece_boundary (ns : List Elegant.Tree.Node)
    (hdims : ∀ n ∈ ns, 0 ≤ n.width ∧ 0 ≤ n.height)
    (p : Elegant.Ishikawa.Params) (spine : Int) (r r' : Elegant.Ishikawa.Rib)
    (h : Elegant.Ishikawa.place ns p spine r = .ok r')
    (i : Nat) (rect : Rect) (pts : List Point)
    (hmem : (i, rect, pts) ∈ r'.pieces) (attach : Int) :
    ∃ q, (pts.map (fun a => ({ x := a.x + attach, y := a.y } : Point))).getLast? =
        some q ∧
      Validator.onBoundary q { rect with x := rect.x + attach } := by
  obtain ⟨q, hlast, hboundary⟩ :=
    place_pieces_boundary ns hdims p spine r r' h i rect pts hmem
  refine ⟨⟨q.x + attach, q.y⟩, ?_, ?_⟩
  · simp only [List.getLast?_map, hlast, Option.map_some]
  · exact onBoundary_shift_x attach hboundary

private def TargetBoundary (out : Elegant.Tree.Layout) : Prop :=
  ∀ (k : Nat) (pts : List Point) (rect : Rect),
    out.routes[k]? = some pts → out.boxes[k]? = some rect →
    pts ≠ [] → ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect

private theorem targetBoundary_set (out : Elegant.Tree.Layout)
    (hinv : TargetBoundary out) (i : Nat) (rect : Rect) (pts : List Point)
    (hpiece : ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect) :
    TargetBoundary ⟨out.boxes.set i rect, out.routes.set i pts⟩ := by
  intro k qs box hqs hbox hne
  by_cases hki : k = i
  · subst k
    by_cases hr : i < out.routes.length
    · by_cases hb : i < out.boxes.length
      · simp [hr, hb] at hqs hbox
        subst qs
        subst box
        exact hpiece
      · simp [hb] at hbox
    · simp [hr] at hqs
  · have hr : out.routes[k]? = some qs := by
      simpa [List.getElem?_set, hki, Ne.symm hki] using hqs
    have hb : out.boxes[k]? = some box := by
      simpa [List.getElem?_set, hki, Ne.symm hki] using hbox
    exact hinv k qs box hr hb hne

private theorem targetBoundary_spine (out : Elegant.Tree.Layout)
    (hinv : TargetBoundary out) (previous spine : Int)
    (hroot : ∀ (rect : Rect), out.boxes[0]? = some rect →
      Validator.onBoundary ⟨0, spine⟩ rect) :
    TargetBoundary ⟨out.boxes,
      out.routes.set 0 [⟨previous, spine⟩, ⟨0, spine⟩]⟩ := by
  intro k pts rect hpts hrect hne
  by_cases hk : k = 0
  · subst k
    by_cases hr : 0 < out.routes.length
    · simp [hr] at hpts
      subst pts
      exact ⟨⟨0, spine⟩, by simp, hroot rect hrect⟩
    · simp [hr] at hpts
  · apply hinv k pts rect ?_ hrect hne
    simpa [List.getElem?_set, hk, Ne.symm hk] using hpts
private theorem assemblePairs_boundary_aux (spine : Int) (n : Nat) :
    ∀ (rs : List Elegant.Ishikawa.Rib) (ceiling previous : Int)
      (out final : Elegant.Tree.Layout),
    rs.length ≤ n →
    (∀ r ∈ rs, ∀ (i : Nat) (rect : Rect) (pts : List Point),
      (i, rect, pts) ∈ r.pieces →
      i ≠ 0 ∧ ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect) →
    TargetBoundary out →
    (∀ (rect : Rect), out.boxes[0]? = some rect →
      Validator.onBoundary ⟨0, spine⟩ rect) →
    Elegant.Ishikawa.assemblePairs spine rs ceiling previous out = .ok final →
    TargetBoundary final := by
  induction n with
  | zero =>
    intro rs ceiling previous out final hlen hpieces hinv hroot hrun
    have hrs : rs = [] := by
      cases rs with
      | nil => rfl
      | cons a rest => simp only [List.length_cons] at hlen; omega
    subst rs
    simp only [Elegant.Ishikawa.assemblePairs, pure, Except.pure,
      Except.ok.injEq] at hrun
    subst final
    exact hinv
  | succ n ih =>
    intro rs ceiling previous out final hlen hpieces hinv hroot hrun
    cases rs with
    | nil =>
      simp only [Elegant.Ishikawa.assemblePairs, pure, Except.pure,
        Except.ok.injEq] at hrun
      subst final
      exact hinv
    | cons a rest =>
      simp only [Elegant.Ishikawa.assemblePairs] at hrun
      obtain ⟨mid, hloop, htail⟩ := bind_ok hrun
      have hm : TargetBoundary mid ∧
          (∀ (rect : Rect), mid.boxes[0]? = some rect →
            Validator.onBoundary ⟨0, spine⟩ rect) := by
        apply forIn_preserves _ _ (fun s => TargetBoundary s ∧
          (∀ (rect : Rect), s.boxes[0]? = some rect →
            Validator.onBoundary ⟨0, spine⟩ rect)) _ _ ⟨hinv, hroot⟩ _ hloop
        intro r hr s next hs hstep
        obtain ⟨inner, hinner, hyield⟩ := bind_ok hstep
        have hrfull : r ∈ a :: rest := by
          simp only [List.mem_cons] at hr ⊢
          rcases hr with he | he
          · exact Or.inl he
          · exact Or.inr (List.mem_of_mem_take he)
        have hi : TargetBoundary inner ∧
            (∀ (rect : Rect), inner.boxes[0]? = some rect →
              Validator.onBoundary ⟨0, spine⟩ rect) := by
          apply forIn_preserves _ _ (fun s => TargetBoundary s ∧
            (∀ (rect : Rect), s.boxes[0]? = some rect →
              Validator.onBoundary ⟨0, spine⟩ rect)) _ _ hs _ hinner
          intro piece hp s₂ s₃ hs₂ h₃
          obtain ⟨i, rect, pts⟩ := piece
          obtain ⟨hi0, q, hlast, hboundary⟩ := hpieces r hrfull i rect pts hp
          split at h₃
          · cases h₃
          · simp only [pure, Except.pure, Except.ok.injEq] at h₃
            subst s₃
            constructor
            · apply targetBoundary_set s₂ hs₂.1
              refine ⟨⟨q.x + _, q.y⟩, ?_, onBoundary_shift_x _ hboundary⟩
              simp only [List.getLast?_map, hlast, Option.map_some]
            · intro box hb
              apply hs₂.2 box
              simpa [List.getElem?_set, hi0, Ne.symm hi0] using hb
        cases next with
        | done s => cases hyield
        | yield s =>
          cases hyield
          exact hi
      apply ih (rest.drop 1) _ _
        ⟨mid.boxes, mid.routes.set 0
          [⟨min ceiling (previous - (Elegant.Ishikawa.extent (a :: rest.take 1)).2) +
              (Elegant.Ishikawa.extent (a :: rest.take 1)).1, spine⟩,
            ⟨0, spine⟩]⟩ final ?_ ?_ ?_ hm.2 htail
      · have hd := drop_one_le rest
        simp only [List.length_cons] at hlen
        omega
      · intro r hr
        exact hpieces r (List.mem_cons_of_mem a (List.mem_of_mem_drop hr))
      · exact targetBoundary_spine mid hm.1 _ spine hm.2

theorem assemblePairs_target_boundary (spine : Int)
    (rs : List Elegant.Ishikawa.Rib) (ceiling previous : Int)
    (out final : Elegant.Tree.Layout)
    (hpieces : ∀ r ∈ rs, ∀ (i : Nat) (rect : Rect) (pts : List Point),
      (i, rect, pts) ∈ r.pieces →
      i ≠ 0 ∧ ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect)
    (hinitial : ∀ (k : Nat) (pts : List Point) (rect : Rect),
      out.routes[k]? = some pts →
      out.boxes[k]? = some rect → pts ≠ [] →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect)
    (hroot : ∀ (rect : Rect), out.boxes[0]? = some rect →
      Validator.onBoundary ⟨0, spine⟩ rect)
    (hrun : Elegant.Ishikawa.assemblePairs spine rs ceiling previous out = .ok final) :
    ∀ (k : Nat) (pts : List Point) (rect : Rect),
      final.routes[k]? = some pts →
      final.boxes[k]? = some rect → pts ≠ [] →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect :=
  assemblePairs_boundary_aux spine rs.length rs ceiling previous out final
    (Nat.le_refl _) hpieces hinitial hroot hrun


theorem normalized_target_boundary (raw placed : Elegant.Tree.Layout)
    (margin : Int) (canvas : Size)
    (hnormal : Tree.normalize margin raw = .ok (canvas, placed))
    (hraw : ∀ (k : Nat) (pts : List Point) (rect : Rect),
      raw.routes[k]? = some pts →
      raw.boxes[k]? = some rect → pts ≠ [] →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect) :
    ∀ (k : Nat) (pts : List Point) (rect : Rect),
      placed.routes[k]? = some pts →
      placed.boxes[k]? = some rect → pts ≠ [] →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect := by
  obtain ⟨dx, dy, hb, hr⟩ := Tree.normalize_records hnormal
  intro k pts rect hpts hrect hne
  rw [hr, List.getElem?_map, Option.map_eq_some_iff] at hpts
  rw [hb, List.getElem?_map, Option.map_eq_some_iff] at hrect
  obtain ⟨qs, hqs, rfl⟩ := hpts
  obtain ⟨box, hbox, rfl⟩ := hrect
  have hqsne : qs ≠ [] := by
    intro he
    subst qs
    exact hne rfl
  obtain ⟨q, hlast, hboundary⟩ := hraw k qs box hqs hbox hqsne
  refine ⟨⟨q.x + dx, q.y + dy⟩, ?_,
    Tree.boundary_translate_raw hboundary dx dy⟩
  simp only [List.getLast?_map, hlast, Option.map_some]

theorem place_piece_index (ns : List Elegant.Tree.Node)
    (p : Elegant.Ishikawa.Params) (spine : Int) (r placed : Elegant.Ishikawa.Rib)
    (hrun : Elegant.Ishikawa.place ns p spine r = .ok placed) :
    ∀ i rect pts, (i, rect, pts) ∈ placed.pieces →
      i = r.cause ∨ ∃ e ∈ r.entries, i = e.node := by
  simp only [Elegant.Ishikawa.place] at hrun
  cases hcause : ns[r.cause]? with
  | none => simp only [hcause] at hrun; cases hrun
  | some cause =>
    simp only [hcause] at hrun
    obtain ⟨mid, hloop, hret⟩ := bind_ok hrun
    have hinv : ∀ i rect pts, (i, rect, pts) ∈ mid.1 →
        i = r.cause ∨ ∃ e ∈ r.entries, i = e.node := by
      apply forIn_preserves _ _ (fun st =>
        ∀ i rect pts, (i, rect, pts) ∈ st.1 →
          i = r.cause ∨ ∃ e ∈ r.entries, i = e.node) _ _ ?_ _ hloop
      · intro i rect pts hmem
        simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        exact Or.inl hmem.1
      · intro a ha state next hi hstep
        obtain ⟨e, idx⟩ := a
        have he : e ∈ r.entries := List.fst_mem_of_mem_zipIdx ha
        cases hpar : state.2[(e.parent + 1).toNat]? with
        | none => simp only [hpar, bind, Except.bind] at hstep; cases hstep
        | some par =>
          cases hpos : r.order.zipIdx.find? (fun v => v.1 == idx) with
          | none => simp only [hpar, hpos, bind, Except.bind] at hstep; cases hstep
          | some pos =>
            by_cases hg : ((e.depth % 2 == 0) &&
                decide (par.t1 ≤ par.t0)) = true
            · simp only [hpar, hpos, hg, ite_true, bind, Except.bind] at hstep
              cases hstep
            · simp only [hpar, hpos, hg, Bool.false_eq_true, ↓reduceIte,
                bind, Except.bind] at hstep
              split at hstep
              all_goals
                cases hn : ns[e.node]? with
                | none => simp only [hn] at hstep; cases hstep
                | some node =>
                  simp only [hn, pure, Except.pure, Except.ok.injEq] at hstep
                  subst next
                  intro i rect pts hmem
                  simp only [ForInStep.value, List.mem_append,
                    List.mem_singleton, Prod.mk.injEq] at hmem
                  rcases hmem with hmem | ⟨rfl, rfl, rfl⟩
                  · exact hi i rect pts hmem
                  · exact Or.inr ⟨e, he, rfl⟩
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
    subst placed
    exact hinv

theorem place_piece_nonzero (ns : List Elegant.Tree.Node)
    (p : Elegant.Ishikawa.Params) (spine : Int) (r placed : Elegant.Ishikawa.Rib)
    (hcause : r.cause ≠ 0)
    (hentries : ∀ e ∈ r.entries, e.node ≠ 0)
    (hrun : Elegant.Ishikawa.place ns p spine r = .ok placed) :
    ∀ i rect pts, (i, rect, pts) ∈ placed.pieces → i ≠ 0 := by
  intro i rect pts hp
  rcases place_piece_index ns p spine r placed hrun i rect pts hp with he | ⟨e, he, hi⟩
  · simpa only [he] using hcause
  · simpa only [hi] using hentries e he

theorem initial_root_boundary (ns : List Elegant.Tree.Node)
    (head : Elegant.Tree.Node) (spine : Int)
    (hhead : ns[0]? = some head)
    (hw : 0 ≤ head.width) (hh : 0 ≤ head.height) :
    ∀ rect : Rect,
      ((List.replicate ns.length (⟨0, 0, 0, 0⟩ : Rect)).set 0
        ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩)[0]? = some rect →
      Validator.onBoundary ⟨0, spine⟩ rect := by
  intro rect hr
  have hlen : 0 < ns.length := by
    cases ns with
    | nil => simp at hhead
    | cons first rest => simp
  simp [hlen] at hr
  subst rect
  have hhalf0 : 0 ≤ Int.fdiv head.height 2 :=
    Int.fdiv_nonneg hh (by decide)
  have hhalf_le : Int.fdiv head.height 2 ≤ head.height := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega
  change 0 ≤ 0 ∧ 0 ≤ 0 + head.width ∧
    spine - Int.fdiv head.height 2 ≤ spine ∧
    spine ≤ spine - Int.fdiv head.height 2 + head.height ∧
    (0 = 0 ∨ 0 = 0 + head.width ∨
      spine = spine - Int.fdiv head.height 2 ∨
      spine = spine - Int.fdiv head.height 2 + head.height)
  exact ⟨by omega, by omega, by omega, by omega, Or.inl rfl⟩

theorem initial_target_boundary (count : Nat) (boxes : List Rect) :
    ∀ (k : Nat) (pts : List Point) (rect : Rect),
      (List.replicate count ([] : List Point))[k]? = some pts →
      boxes[k]? = some rect → pts ≠ [] →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect := by
  intro k pts rect hpts _ hne
  have hempty : pts = [] := by
    have hm := List.mem_replicate.mp (List.mem_of_getElem? hpts)
    simpa using hm.2
  exact False.elim (hne hempty)

theorem children_nonzero (ns : List Elegant.Tree.Node) (head : Elegant.Tree.Node)
    (hhead : ns[0]? = some head) (hroot : head.parent = none)
    (parent i : Nat) (hi : i ∈ Elegant.Ishikawa.children ns parent) : i ≠ 0 := by
  intro hz
  subst i
  simp [Elegant.Ishikawa.children, hhead, hroot] at hi

theorem flatten_nonzero (ns : List Elegant.Tree.Node)
    (hchildren : ∀ parent i, i ∈ Elegant.Ishikawa.children ns parent → i ≠ 0)
    (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth : Nat)
      (entries : List Elegant.Ishikawa.Entry) (order : List Nat),
      (∀ i ∈ ids, i ≠ 0) →
      (∀ e ∈ entries, e.node ≠ 0) →
      ∀ e ∈ (Elegant.Ishikawa.flatten ns up fuel ids par depth entries order).1,
        e.node ≠ 0 := by
  induction fuel with
  | zero =>
    intro ids par depth entries order _ he
    exact he
  | succ fuel ih =>
    intro ids par depth entries order hids he
    have hwalk : ∀ i ∈ (if up then ids.reverse else ids), i ≠ 0 := by
      cases up <;> simpa using hids
    unfold Elegant.Ishikawa.flatten
    generalize (if up then ids.reverse else ids) = walk at hwalk ⊢
    induction walk generalizing entries order with
    | nil => exact he
    | cons node rest tail =>
      simp only [List.foldl_cons]
      have hn : node ≠ 0 := hwalk node (List.mem_cons_self ..)
      have happend : ∀ e ∈ entries ++
          [({ node := node, parent := par, depth := depth } : Elegant.Ishikawa.Entry)],
          e.node ≠ 0 := by
        intro e hm
        rcases List.mem_append.mp hm with hm | hm
        · exact he e hm
        · simp only [List.mem_singleton] at hm
          subst e
          exact hn
      have hrec := ih (Elegant.Ishikawa.children ns node) (entries.length : Int)
        (depth + 1) (entries ++ [⟨node, par, depth⟩])
        (if depth % 2 == 0 then order ++ [entries.length] else order)
        (hchildren node) happend
      apply tail
      · exact hrec
      · intro i hi
        exact hwalk i (List.mem_cons_of_mem node hi)

theorem successful_link (ns : List Elegant.Tree.Node) (p : Elegant.Ishikawa.Params)
    (raw : Elegant.Tree.Layout)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw) :
    Elegant.Tree.link ns = true := by
  cases ns with
  | nil => rfl
  | cons head rest =>
    unfold Elegant.Ishikawa.layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    cases hl : Elegant.Tree.link (head :: rest) with
    | false => simp [hl, bind, Except.bind] at hrun
    | true => rfl

theorem successful_children_nonzero (ns : List Elegant.Tree.Node)
    (p : Elegant.Ishikawa.Params) (raw : Elegant.Tree.Layout)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (parent i : Nat) (hi : i ∈ Elegant.Ishikawa.children ns parent) : i ≠ 0 := by
  have hv := Elegant.Tree.link_valid (successful_link ns p raw hrun)
  cases hh : ns[0]? with
  | none =>
    intro hz
    subst i
    simp [Elegant.Ishikawa.children, hh] at hi
  | some head =>
    have hp : head.parent = none := by
      simpa [Elegant.Tree.parentOf, hh] using hv.rootNone
    exact children_nonzero ns head hh hp parent i hi

theorem successful_initial_root_boundary (ns : List Elegant.Tree.Node)
    (p : Elegant.Ishikawa.Params) (raw : Elegant.Tree.Layout)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (head : Elegant.Tree.Node) (hhead : ns[0]? = some head) (spine : Int) :
    ∀ rect : Rect,
      ((List.replicate ns.length (⟨0, 0, 0, 0⟩ : Rect)).set 0
        ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩)[0]? = some rect →
      Validator.onBoundary ⟨0, spine⟩ rect := by
  have hv := Elegant.Tree.link_valid (successful_link ns p raw hrun)
  obtain ⟨hw, hh⟩ := hv.dims head (List.mem_of_getElem? hhead)
  exact initial_root_boundary ns head spine hhead (by omega) (by omega)

theorem successful_flattened_rib_pieces (ns : List Elegant.Tree.Node)
    (p : Elegant.Ishikawa.Params) (raw : Elegant.Tree.Layout)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (cause k : Nat) (hcause : cause ∈ Elegant.Ishikawa.children ns 0)
    (spine length heights : Int) (placed : Elegant.Ishikawa.Rib)
    (hplace : Elegant.Ishikawa.place ns p spine
      { cause := cause, upper := Elegant.Ishikawa.upper k,
        entries := (Elegant.Ishikawa.flatten ns (Elegant.Ishikawa.upper k) 64
          (Elegant.Ishikawa.children ns cause) (-1) 2 [] []).1,
        order := (Elegant.Ishikawa.flatten ns (Elegant.Ishikawa.upper k) 64
          (Elegant.Ishikawa.children ns cause) (-1) 2 [] []).2,
        heights := heights, length := length } = .ok placed) :
    ∀ i rect pts, (i, rect, pts) ∈ placed.pieces →
      i ≠ 0 ∧ ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect := by
  have hchildren := successful_children_nonzero ns p raw hrun
  have hentries := flatten_nonzero ns hchildren (Elegant.Ishikawa.upper k) 64
    (Elegant.Ishikawa.children ns cause) (-1) 2 [] []
    (hchildren cause) (by simp)
  have hdims : ∀ n ∈ ns, 0 ≤ n.width ∧ 0 ≤ n.height := by
    intro n hn
    obtain ⟨hw, hh⟩ := (Elegant.Tree.link_valid (successful_link ns p raw hrun)).dims n hn
    exact ⟨by omega, by omega⟩
  intro i rect pts hp
  constructor
  · exact place_piece_nonzero ns p spine _ placed (hchildren 0 cause hcause)
      hentries hplace i rect pts hp
  · exact place_pieces_boundary ns hdims p spine _ placed hplace i rect pts hp

set_option maxHeartbeats 800000 in
theorem raw_target_boundary (ns : List Elegant.Tree.Node)
    (p : Elegant.Ishikawa.Params) (raw : Elegant.Tree.Layout)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw) :
    ∀ (k : Nat) (pts : List Point) (rect : Rect),
      raw.routes[k]? = some pts → raw.boxes[k]? = some rect → pts ≠ [] →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect := by
  have hv := Elegant.Tree.link_valid (successful_link ns p raw hrun)
  have hdims : ∀ n ∈ ns, 0 ≤ n.width ∧ 0 ≤ n.height := by
    intro n hn
    obtain ⟨hw, hh⟩ := hv.dims n hn
    exact ⟨by omega, by omega⟩
  have hchildren := successful_children_nonzero ns p raw hrun
  cases ns with
  | nil =>
    have he := layout_empty_nodes p raw hrun
    subst raw
    intro k pts rect hp
    simp at hp
  | cons head rest =>
    unfold Elegant.Ishikawa.layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    by_cases hlink : ((!Tree.link (head :: rest)) ||
        ((head :: rest).any fun n => n.width < 1 || n.height < 1)) = true
    · rw [ite_eq_left hlink] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
    · rw [ite_eq_right hlink] at hrun
      by_cases hparams : (p.spineBase < 5 || p.ribMin < 5 || p.ribPool < 1 ||
          p.spacing < 1 || p.stub < 1 || p.base < 1 || p.perChild < 0 ||
          p.inset < 0 || p.cos < 0 || p.sin < 1) = true
      · rw [ite_eq_left hparams] at hrun
        simp only [bind, Except.bind] at hrun
        cases hrun
      · rw [ite_eq_right hparams] at hrun
        obtain ⟨ribs, hribs, hnext⟩ := bind_ok hrun
        have hrib_indices : ∀ r ∈ ribs,
            r.cause ≠ 0 ∧ ∀ e ∈ r.entries, e.node ≠ 0 := by
          apply forIn_preserves _ _ (fun rs =>
            ∀ r ∈ rs, r.cause ≠ 0 ∧ ∀ e ∈ r.entries, e.node ≠ 0)
            _ _ (by simp) _ hribs
          intro entry hentry state next hi hstep
          simp only [pure, Except.pure, Except.ok.injEq] at hstep
          subst next
          intro r hr
          simp only [ForInStep.value, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | hr
          · exact hi r hr
          · subst r
            constructor
            · exact hchildren 0 entry.1 (List.fst_mem_of_mem_zipIdx hentry)
            · exact flatten_nonzero _ hchildren _ _ _ _ _ _ _
                (hchildren entry.1) (by simp)
        let total (up : Bool) : Int :=
          ((ribs.filter (fun r => r.upper == up)).map
            (fun r => (r.entries.length : Int))).sum
        let all := total true + total false
        let length (up : Bool) :=
          let initial := if all > 0 then
            max p.ribMin (Int.fdiv (p.ribPool * total up) all) else p.spineBase
          (ribs.filter (fun r => r.upper == up)).foldl (fun l r =>
            if r.entries.isEmpty then l else
              max l (max ((r.entries.length : Int) * p.spacing)
                ((r.entries.length + 1 : Nat) * r.heights))) initial
        let spine := max (length true) p.spineBase
        change (do
          let placedRibs ← ribs.mapM (fun (r : Elegant.Ishikawa.Rib) =>
            Elegant.Ishikawa.place (head :: rest) p spine
              { r with length := if (Elegant.Ishikawa.children
                  (head :: rest) r.cause).isEmpty then
                    Int.fdiv (length r.upper) 5 else length r.upper })
          let some root := (head :: rest)[0]? | throw LayoutError.domain
          Elegant.Ishikawa.assemblePairs spine placedRibs (-p.inset) 0
            ⟨(List.replicate (head :: rest).length (⟨0, 0, 0, 0⟩ : Rect)).set 0
                ⟨0, spine - Int.fdiv root.height 2, root.width, root.height⟩,
              List.replicate (head :: rest).length []⟩) = .ok raw at hnext
        obtain ⟨placedRibs, hplaces, hassemble⟩ := bind_ok hnext
        have hpieces : ∀ r ∈ placedRibs, ∀ i rect pts,
            (i, rect, pts) ∈ r.pieces →
            i ≠ 0 ∧ ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect := by
          intro r hr
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
          obtain ⟨source, hsource, hplace⟩ :=
            (Elegant.Kinds.Gitgraph.mapM_index_record _ _ _ hplaces).2 j r hj
          obtain ⟨hcause, hentries⟩ :=
            hrib_indices source (List.mem_of_getElem? hsource)
          intro i rect pts hp
          constructor
          · exact place_piece_nonzero (head :: rest) p spine
              { source with length := if (Elegant.Ishikawa.children
                  (head :: rest) source.cause).isEmpty then
                    Int.fdiv (length source.upper) 5 else length source.upper }
              r hcause hentries hplace i rect pts hp
          · exact place_pieces_boundary _ hdims p spine _ r hplace i rect pts hp
        simp only [List.getElem?_cons_zero] at hassemble
        obtain ⟨hw, hh⟩ := hv.dims head (List.mem_cons_self ..)
        apply assemblePairs_target_boundary _ placedRibs _ _ _ raw hpieces
          (initial_target_boundary _ _) ?_ hassemble
        exact initial_root_boundary _ head _ (by rfl) (by omega) (by omega)

theorem successful_normalized_target_boundary (ns : List Elegant.Tree.Node)
    (p : Elegant.Ishikawa.Params) (raw placed : Elegant.Tree.Layout)
    (margin : Int) (canvas : Size)
    (hlayout : Elegant.Ishikawa.layout ns p = .ok raw)
    (hnormal : Tree.normalize margin raw = .ok (canvas, placed)) :
    ∀ (k : Nat) (pts : List Point) (rect : Rect),
      placed.routes[k]? = some pts → placed.boxes[k]? = some rect → pts ≠ [] →
      ∃ q, pts.getLast? = some q ∧ Validator.onBoundary q rect :=
  normalized_target_boundary raw placed margin canvas hnormal
    (raw_target_boundary ns p raw hlayout)

theorem box_find_of_index (boxes : List Box)
    (hunique : (boxes.map (·.id)).Nodup) (i : Nat) (box : Box)
    (hbox : boxes[i]? = some box) :
    boxes.find? (fun b => b.id == box.id) = some box := by
  induction boxes generalizing i with
  | nil => simp at hbox
  | cons first rest ih =>
    rcases List.nodup_cons.mp hunique with ⟨habsent, hrest⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hbox
      subst box
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at hbox
      have hne : (first.id == box.id) = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        have hid : first.id = box.id := by simpa using he
        exact habsent (List.mem_map.mpr
          ⟨box, List.mem_of_getElem? hbox, hid.symm⟩)
      simp only [List.find?_cons, hne]
      exact ih hrest i hbox

theorem box_set_ids (boxes : List Box) (i : Nat) (box : Box)
    (hbox : boxes[i]? = some box) (rect : Rect) :
    ((boxes.set i { box with rect := rect }).map (·.id)) =
      boxes.map (·.id) := by
  induction boxes generalizing i with
  | nil => simp at hbox
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hbox
      subst box
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hbox
      simpa only [List.set_cons_succ, List.map_cons] using
        congrArg (List.cons first.id) (ih i hbox)

theorem firstpoint_replacement_boundary (boxes : List Box) (i : Nat)
    (anchor : Box) (a : Point)
    (hunique : (boxes.map (·.id)).Nodup)
    (hanchor : boxes[i]? = some anchor) :
    let replacement := { anchor with rect := (⟨a.x, a.y, 0, 0⟩ : Rect) }
    (boxes.set i replacement).find? (fun b => b.id == anchor.id) =
      some replacement ∧ Validator.onBoundary a replacement.rect := by
  dsimp only
  constructor
  · have hids := box_set_ids boxes i anchor hanchor ⟨a.x, a.y, 0, 0⟩
    have hget : (boxes.set i { anchor with rect := ⟨a.x, a.y, 0, 0⟩ })[i]? =
        some { anchor with rect := ⟨a.x, a.y, 0, 0⟩ } := by
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hanchor
      simp [hi]
    exact box_find_of_index _ (by rw [hids]; exact hunique) i _ hget
  · simp [Validator.onBoundary]

private theorem forIn_index_invariant {α β : Type} (xs : List α) (start : Nat)
    (initial final : β) (step : α × Nat → β → Except LayoutError (ForInStep β))
    (P : Nat → β → Prop) (hinit : P start initial)
    (hstep : ∀ a i state next, P i state → step (a, i) state = .ok next →
      ∃ state', next = .yield state' ∧ P (i + 1) state')
    (hrun : forIn (xs.zipIdx start) initial step = .ok final) :
    P (start + xs.length) final := by
  induction xs generalizing start initial with
  | nil =>
    change Except.ok initial = Except.ok final at hrun
    cases hrun
    exact hinit
  | cons a xs ih =>
    rw [List.zipIdx_cons, List.forIn_cons] at hrun
    cases hs : step (a, start) initial with
    | error err => simp [hs, bind, Except.bind] at hrun
    | ok next =>
      obtain ⟨state, rfl, hinv⟩ := hstep a start initial next hinit hs
      simp only [hs, bind, Except.bind] at hrun
      have hlen : start + 1 + xs.length = start + (a :: xs).length := by
        simp only [List.length_cons]
        omega
      rw [← hlen]
      exact ih (start + 1) state hinv hrun

theorem firstpoint_replacement_preserves_target (boxes : List Box) (anchor : Box)
    (n j k : Nat) (point : Point) (target : Box)
    (hk : k < n) (hbox : boxes[k]? = some target) :
    (boxes.set (n + j) { anchor with rect := ⟨point.x, point.y, 0, 0⟩ })[k]? =
      some target := by
  have hne : k ≠ n + j := by omega
  simpa [List.getElem?_set, hne, Ne.symm hne] using hbox

theorem firstpoint_replacement_preserves_previous (boxes : List Box) (anchor : Box)
    (n previous current : Nat) (point : Point) (source : Box)
    (hprevious : previous < current)
    (hbox : boxes[n + previous]? = some source) :
    (boxes.set (n + current) { anchor with rect := ⟨point.x, point.y, 0, 0⟩ })[n + previous]? =
      some source := by
  have hne : n + previous ≠ n + current := by omega
  have hindex : current ≠ previous := by omega
  simpa [List.getElem?_set, hne, Ne.symm hne, hindex] using hbox

private theorem assemblePairs_lengths_aux (spine : Int) (fuel : Nat) :
    ∀ (ribs : List Elegant.Ishikawa.Rib) (ceiling previous : Int)
      (initial final : Tree.Layout),
    ribs.length ≤ fuel →
    Elegant.Ishikawa.assemblePairs spine ribs ceiling previous initial = .ok final →
    final.boxes.length = initial.boxes.length ∧
      final.routes.length = initial.routes.length := by
  induction fuel with
  | zero =>
    intro ribs ceiling previous initial final hlen hrun
    cases ribs with
    | nil =>
      simp only [Elegant.Ishikawa.assemblePairs, pure, Except.pure,
        Except.ok.injEq] at hrun
      subst final
      exact ⟨rfl, rfl⟩
    | cons first rest => simp only [List.length_cons] at hlen; omega
  | succ fuel ih =>
    intro ribs ceiling previous initial final hlen hrun
    cases ribs with
    | nil =>
      simp only [Elegant.Ishikawa.assemblePairs, pure, Except.pure,
        Except.ok.injEq] at hrun
      subst final
      exact ⟨rfl, rfl⟩
    | cons first rest =>
      simp only [Elegant.Ishikawa.assemblePairs] at hrun
      obtain ⟨mid, hloop, htail⟩ := bind_ok hrun
      have hmid : mid.boxes.length = initial.boxes.length ∧
          mid.routes.length = initial.routes.length := by
        apply forIn_preserves _ _ (fun out =>
          out.boxes.length = initial.boxes.length ∧
            out.routes.length = initial.routes.length) _ _ ⟨rfl, rfl⟩ _ hloop
        intro rib _ state next hinv hstep
        obtain ⟨inner, hinner, hyield⟩ := bind_ok hstep
        have hinner_lengths : inner.boxes.length = initial.boxes.length ∧
            inner.routes.length = initial.routes.length := by
          apply forIn_preserves _ _ (fun out =>
            out.boxes.length = initial.boxes.length ∧
              out.routes.length = initial.routes.length) _ _ hinv _ hinner
          intro piece _ out next hout hnext
          split at hnext
          · cases hnext
          · simp only [pure, Except.pure, Except.ok.injEq] at hnext
            subst next
            simpa only [ForInStep.value, List.length_set] using hout
        cases next with
        | done out => cases hyield
        | yield out => cases hyield; exact hinner_lengths
      have hrest : (rest.drop 1).length ≤ fuel := by
        have hd := drop_one_le rest
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨hb, hr⟩ := ih _ _ _ _ _ hrest htail
      constructor
      · exact hb.trans hmid.1
      · have hr' : final.routes.length = mid.routes.length := by
          simpa only [List.length_set] using hr
        exact hr'.trans hmid.2

theorem successful_raw_lengths (ns : List Tree.Node) (p : Elegant.Ishikawa.Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw) :
    raw.boxes.length = ns.length ∧ raw.routes.length = ns.length := by
  cases ns with
  | nil =>
    have he := layout_empty_nodes p raw hrun
    subst raw
    exact ⟨rfl, rfl⟩
  | cons head rest =>
    unfold Elegant.Ishikawa.layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    split at hrun
    · simp only [bind, Except.bind] at hrun; cases hrun
    · split at hrun
      · simp only [bind, Except.bind] at hrun; cases hrun
      · obtain ⟨ribs, _, hnext⟩ := bind_ok hrun
        obtain ⟨placed, _, hassemble⟩ := bind_ok hnext
        simp only [List.getElem?_cons_zero] at hassemble
        have hl := assemblePairs_lengths_aux _ placed.length placed _ _ _ _
          (Nat.le_refl _) hassemble
        simpa only [List.length_set, List.length_replicate] using hl

theorem successful_normalized_lengths (ns : List Tree.Node)
    (p : Elegant.Ishikawa.Params) (raw placed : Tree.Layout)
    (margin : Int) (canvas : Size)
    (hlayout : Elegant.Ishikawa.layout ns p = .ok raw)
    (hnormal : Tree.normalize margin raw = .ok (canvas, placed)) :
    placed.boxes.length = ns.length ∧ placed.routes.length = ns.length := by
  obtain ⟨dx, dy, hplaced⟩ := Tree.normalize_translate hnormal
  subst placed
  simpa only [Tree.Layout.translate, List.length_map] using
    successful_raw_lengths ns p raw hlayout

private theorem append_map_loop {α β : Type} (xs : List α) (f : α → β)
    (out : List β)
    (hrun : forIn xs ([] : List β) (fun a state =>
      pure (.yield (state ++ [f a]))) = (Except.ok out : Except LayoutError _)) :
    out = xs.map f := by
  have hp : out = ([] ++ xs).map f := by
    apply Elegant.forIn_processed [] xs [] out _ (fun done state =>
      state = done.map f) (by rfl) ?_ hrun
    intro done a rest state next _ hinv hstep
    simp only [pure, Except.pure, Except.ok.injEq] at hstep
    subst next
    refine ⟨state ++ [f a], rfl, ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hinv]
  simpa using hp

private def initialSceneBox (placed : Tree.Layout) (b : ModelBox) (i : Nat) : Box :=
  ⟨b.id, b.role.id, (placed.boxes[i]?).getD ⟨0, 0, 0, 0⟩, b.parent, b.exclusive⟩

private theorem initialSceneBox_ids (xs : List ModelBox) (placed : Tree.Layout)
    (start : Nat) :
    ((xs.zipIdx start).map (fun entry =>
      initialSceneBox placed entry.1 entry.2)).map (·.id) = xs.map (·.id) := by
  induction xs generalizing start with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.zipIdx_cons, List.map_cons, initialSceneBox]
    exact congrArg (List.cons first.id) (ih (start + 1))

private theorem initialSceneBox_at (xs : List ModelBox) (placed : Tree.Layout)
    (start i : Nat) (b : ModelBox) (hb : xs[i]? = some b) :
    ((xs.zipIdx start).map (fun entry =>
      initialSceneBox placed entry.1 entry.2))[i]? =
        some (initialSceneBox placed b (start + i)) := by
  induction xs generalizing start i with
  | nil => simp at hb
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst b
      simp [List.zipIdx_cons]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hb
      have hsum : start + 1 + i = start + (i + 1) := by omega
      simpa only [List.zipIdx_cons, List.map_cons, List.getElem?_cons_succ,
        hsum] using ih (start + 1) i hb

def SceneRouteNativeSource (m : Model) (input : Elegant.Kinds.Ishikawa.Input)
    (normalized : Tree.Layout) (route : Route) : Prop :=
  ∃ (targetIndex : Nat) (target : ModelBox), targetIndex < input.nodes.length ∧
    m.boxes[targetIndex]? = some target ∧ target.id = route.toId ∧
    normalized.routes[targetIndex]? = some route.points

private def SceneRoutePorts (m : Model) (input : Elegant.Kinds.Ishikawa.Input)
    (normalized : Tree.Layout) (n processed : Nat) (boxes : List Box)
    (routes : List Route) : Prop :=
  ∀ r ∈ routes, ∃ sourceIndex targetIndex, sourceIndex < processed ∧ targetIndex < n ∧
    ∃ source target : Box, ∃ first last : Point,
      boxes[n + sourceIndex]? = some source ∧ boxes[targetIndex]? = some target ∧
      source.id = r.fromId ∧ target.id = r.toId ∧
      r.points.head? = some first ∧ r.points.getLast? = some last ∧
      Validator.onBoundary first source.rect ∧ Validator.onBoundary last target.rect ∧
      SceneRouteNativeSource m input normalized r

private theorem sceneRoutePorts_set (m : Model) (input : Elegant.Kinds.Ishikawa.Input)
    (normalized : Tree.Layout) (n processed : Nat) (boxes : List Box)
    (routes : List Route) (anchor : Box) (point : Point)
    (hinv : SceneRoutePorts m input normalized n processed boxes routes) :
    SceneRoutePorts m input normalized n (processed + 1)
      (boxes.set (n + processed) { anchor with rect := ⟨point.x, point.y, 0, 0⟩ })
      routes := by
  intro r hr
  obtain ⟨si, ti, hsi, hti, source, target, first, last,
    hs, ht, hsid, htid, hf, hl, hfb, hlb, hnative⟩ := hinv r hr
  exact ⟨si, ti, by omega, hti, source, target, first, last,
    firstpoint_replacement_preserves_previous boxes anchor n si processed point source hsi hs,
    firstpoint_replacement_preserves_target boxes anchor n processed ti point target hti ht,
    hsid, htid, hf, hl, hfb, hlb, hnative⟩

theorem successful_scene_c5_sources (m : Model) (s : Scene) (hwf : WellFormed m)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) :
    Validator.C5 s.layoutDump ∧
      ∃ (input : Elegant.Kinds.Ishikawa.Input) (raw normalized : Tree.Layout) (canvas : Size),
        Elegant.Kinds.Ishikawa.decode m = .ok input ∧
        Elegant.Ishikawa.layout input.nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw ∧
        Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw = .ok (canvas, normalized) ∧
        ∀ route ∈ s.routes, SceneRouteNativeSource m input normalized route := by
  unfold Elegant.Kinds.Ishikawa.scene at hs
  obtain ⟨input, hinput, hs⟩ := bind_ok hs
  obtain ⟨raw, hraw, hs⟩ := bind_ok hs
  obtain ⟨pair, hnormal, hs⟩ := bind_ok hs
  have hlength := successful_normalized_lengths input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) raw pair.2
    (LayoutConst.canvas_margin.get m.profile) pair.1 hraw hnormal
  have htarget := successful_normalized_target_boundary input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) raw pair.2
    (LayoutConst.canvas_margin.get m.profile) pair.1 hraw hnormal
  obtain ⟨boxes0, hboxes0, hs⟩ := bind_ok hs
  have hboxes : boxes0 = (m.boxes.zipIdx).map (fun entry =>
      initialSceneBox pair.2 entry.1 entry.2) :=
    append_map_loop _ _ _ hboxes0
  obtain ⟨triple, hloop, hrest⟩ := bind_ok hs
  let P (processed : Nat) (state : List Box × List Route × List Group) : Prop :=
    state.1.map (·.id) = m.boxes.map (·.id) ∧
    (∀ i box, m.boxes[i]? = some box → i < input.nodes.length →
      state.1[i]? = some (initialSceneBox pair.2 box i)) ∧
    SceneRoutePorts m input pair.2 input.nodes.length processed state.1 state.2.1
  have hfinal : P m.routes.length triple := by
    refine Nat.zero_add m.routes.length ▸
      forIn_index_invariant m.routes 0 _ triple _ P ?_ ?_ hloop
    · constructor
      · rw [hboxes]
        exact initialSceneBox_ids m.boxes pair.2 0
      · constructor
        · intro i box hbox _
          rw [hboxes]
          simpa only [Nat.zero_add] using initialSceneBox_at m.boxes pair.2 0 i box hbox
        · intro route hroute
          simp at hroute
    · intro route j state next hinv hstep
      obtain ⟨hids, hnodes, hports⟩ := hinv
      cases hfind : (m.boxes.take input.nodes.length).findIdx? (·.id == route.toId) with
      | none => simp only [hfind, bind, Except.bind] at hstep; cases hstep
      | some k =>
        cases hdepth : input.depths[k]? with
        | none => simp only [hfind, hdepth, bind, Except.bind] at hstep; cases hstep
        | some depth =>
          by_cases horth : (!Elegant.Kinds.Ishikawa.consistentOrthogonal
              depth route.orthogonal) = true
          · simp only [hfind, hdepth, horth, bind, Except.bind, ite_true] at hstep
            cases hstep
          · cases hanchor : state.1[input.nodes.length + j]? with
            | none =>
              simp only [hfind, hdepth, horth, hanchor, bind, Except.bind] at hstep
              cases hstep
            | some anchor =>
              cases hpoints : pair.2.routes[k]? with
              | none =>
                simp only [hfind, hdepth, horth, hanchor, hpoints,
                  bind, Except.bind] at hstep
                cases hstep
              | some points =>
                cases points with
                | nil =>
                  simp only [hfind, hdepth, horth, hanchor, hpoints,
                    bind, Except.bind] at hstep
                  cases hstep
                | cons first tail =>
                  cases tail with
                  | nil =>
                    simp only [hfind, hdepth, horth, hanchor, hpoints,
                      bind, Except.bind] at hstep
                    cases hstep
                  | cons second remaining =>
                    by_cases hid : (anchor.id != route.fromId) = true
                    · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                        bind, Except.bind, ite_true] at hstep
                      cases hstep
                    · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                        Bool.false_eq_true, ite_false, bind, Except.bind,
                        pure, Except.pure, Except.ok.injEq] at hstep
                      subst next
                      refine ⟨_, rfl, ?_⟩
                      constructor
                      · exact (box_set_ids state.1 _ anchor hanchor _).trans hids
                      · constructor
                        · intro i box hbox hi
                          exact firstpoint_replacement_preserves_target state.1 anchor
                            input.nodes.length j i first _ hi (hnodes i box hbox hi)
                        · intro emitted hemitted
                          simp only [List.mem_append, List.mem_singleton] at hemitted
                          rcases hemitted with hold | rfl
                          · exact sceneRoutePorts_set m input pair.2 input.nodes.length j
                              state.1 state.2.1 anchor first hports emitted hold
                          · obtain ⟨hk, hmatch, _⟩ :=
                              List.findIdx?_eq_some_iff_getElem.mp hfind
                            have hkn : k < input.nodes.length := by
                              have hk' := hk
                              simp only [List.length_take] at hk'
                              omega
                            have hkm : k < m.boxes.length := by
                              have hk' := hk
                              simp only [List.length_take] at hk'
                              omega
                            let mb := m.boxes[k]'hkm
                            have hmb : m.boxes[k]? = some mb :=
                              List.getElem?_eq_getElem hkm
                            have hmbid : mb.id = route.toId := by
                              simpa only [List.getElem_take, beq_iff_eq] using hmatch
                            have hnode := hnodes k mb hmb hkn
                            have hkr : k < pair.2.boxes.length := by omega
                            let rect := pair.2.boxes[k]'hkr
                            have hrect : pair.2.boxes[k]? = some rect :=
                              List.getElem?_eq_getElem hkr
                            obtain ⟨last, hlast, hboundary⟩ :=
                              htarget k (first :: second :: remaining) rect
                                hpoints hrect (by simp)
                            have haid : anchor.id = route.fromId := by
                              simpa using hid
                            have hnew : (state.1.set (input.nodes.length + j)
                                { anchor with rect := ⟨first.x, first.y, 0, 0⟩ })[input.nodes.length + j]? =
                                some { anchor with rect := ⟨first.x, first.y, 0, 0⟩ } := by
                              obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hanchor
                              simp [hi]
                            refine ⟨j, k, by omega, hkn, _, _, first, last,
                              hnew, firstpoint_replacement_preserves_target state.1 anchor
                                input.nodes.length j k first _ hkn hnode,
                              haid, hmbid, rfl, hlast, ?_, ?_, ?_⟩
                            · simp [Validator.onBoundary]
                            · simpa only [initialSceneBox, hrect, Option.getD_some] using hboundary
                            · exact ⟨k, mb, hkn, hmb, hmbid, hpoints⟩
  obtain ⟨groups, _, hret⟩ := bind_ok hrest
  simp only [pure, Except.pure, Except.ok.injEq] at hret
  subst s
  refine ⟨?_, input, raw, pair.2, pair.1, hinput, hraw, hnormal, ?_⟩
  · intro route hroute
    obtain ⟨si, ti, _, _, source, target, first, last,
      hsource, htargetbox, hsid, htid, hf, hl, hfb, hlb, hnative⟩ :=
        hfinal.2.2 route hroute
    have hnodup : (triple.1.map (·.id)).Nodup := by
      rw [hfinal.1]
      exact Model.boxIds_nodup hwf
    refine ⟨first, last, source, target, hf, hl, ?_, ?_, hfb, hlb⟩
    · change triple.1.find? (fun b => b.id == route.fromId) = some source
      rw [← hsid]
      exact box_find_of_index _ hnodup _ source hsource
    · change triple.1.find? (fun b => b.id == route.toId) = some target
      rw [← htid]
      exact box_find_of_index _ hnodup _ target htargetbox
  · intro route hroute
    obtain ⟨si, ti, hsi, hti, source, target, first, last,
      hsource, htarget, hsid, htid, hf, hl, hfb, hlb, hnative⟩ :=
        hfinal.2.2 route hroute
    exact hnative

theorem successful_scene_c5 (m : Model) (s : Scene) (hwf : WellFormed m)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) :
    Validator.C5 s.layoutDump :=
  (successful_scene_c5_sources m s hwf hs).1

theorem ishikawa_c5 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (_limits : WithinLimits m)
    (hlayout : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C5 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ :=
    Elegant.Kinds.Ishikawa.layout_success_scene m result hlayout
  rw [hdump]
  exact successful_scene_c5 m s hwf hs

end Elegant.Kinds.IshikawaValid
