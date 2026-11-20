import Elegant.Layered.NotesFlatLabelClauses
import Elegant.Layered.NotesMirrorFacts
import Elegant.Layered.NotesPlacementFacts
import Elegant.Layered.NotesLabelGeomFacts
import Elegant.Layered.NotesC8aRoleRepair
import Elegant.Layered.NotesRouteFacts

set_option autoImplicit false

open Elegant Layered PipelineImpl

/-!
# Note-stage C6/C8a geometry and fragment first-wins (residuals).

Proved here:
* `NotesC6Geom` from the single bridge `Nc68C6BridgeW` plus local
  well-formedness (`nc68C6Geom_of_bridgeW`). The two exclusivity conjuncts come
  from the box mirrors (`ngfC6BoxExclC/F_holds` via `notesContractMirror_holds` /
  `notesFragMirror_holds`); the other eight are reassembled from the bridge.
* `NotesC8aGeomT` from `Nc68C8aBridgeW` and local well-formedness
  (`nc68C8aGeomT_of_bridgeW`). The contraction fold and the base scene mirror
  establish parent transfer and the contracted length bound.
* Guarded `notesFragFirstWins` from lookup uniqueness
  (`nc68_fragFirstWins_of_unique` via `notesFirstMatch_holds`).

The bridges quantify over executed `NotesExecution` runs.

False as stated: unconditional `notesFragFirstWins` over arbitrary fragment
lists. Witness: `p1` with box `("x", ⟨0,0,1,1⟩)`, `dx/dy = 0/0` and `p2` with the
same box id, `dx/dy = 10/0`. Then `p2.rect "x" = some ⟨10,0,1,1⟩` but
`[p1,p2].findSome? (·.rect "x") = some ⟨0,0,1,1⟩`, so the `p2` instance fails.
True form (proved): on executed fragments with holding-rect (`hSelf`) and
cross-absence (`hCross`), the lookup returns the holding fragment; this is what
`notesFragBoxFirst` consumes via `notesFragBoxFirst_holds`.

Probe (`proofs/wip/Probe/NotesGeomC68T_probe.lean`): `self/cross/baseC/top/len/
roleT/fRole/found/clear` and `ancC/ancF/flagsKept/flagsFrag/keptFrag/fragCon/
fragOther/routerClear` are all `true` on state, group, two-note, empty-text,
and zero-size inputs; the self-loop input is rejected with
`LayoutError.domain`. C8aT `topNodup/fold/len/contractScene/cRoleT/mirror/
fRole/found/clear/fragDisj/sceneAnc/env/envDisj` are all `true` on state,
group, solo, bare-group, empty, and two-note inputs
(`NotesC8aRoleRepair.lean` `#eval ncrrGeomTBool`).
-/
/-! ### Bundle-top uniqueness (`NotesC8aTopNodup` from `bundlesOf` target
    uniqueness, proved on the actual `NotesExecution`) -/

private theorem htu_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem htu_mapM_mem {α β : Type} {f : α → Except LayoutError β} :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, _, hy => by
    have h2 : ([] : List β) = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst h2
    cases hy
  | _ :: _, ys, h, y, hy => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := htu_bind_ok h
    obtain ⟨bs, hbs, h⟩ := htu_bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    subst hys
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, hfb⟩
    · obtain ⟨x, hx, hfx⟩ := htu_mapM_mem _ bs hbs y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

open scoped Classical in
private theorem htu_mapM_exists_map {α : Type} (f : α → Except LayoutError BundleLayout) :
    ∀ {l : List α} {ys : List BundleLayout}, l.mapM f = .ok ys →
      ∃ g : α → BundleLayout, ys = l.map g ∧ ∀ x ∈ l, f x = .ok (g x) := by
  intro l
  induction l with
  | nil =>
    intro ys h
    refine ⟨fun _ => ⟨{ id := "" }, ⟨0, []⟩,
      { scene := { kind := "", canvas := ⟨0, 0⟩ }, budgetExhausted := false, itemArea := 0 },
      [], ⟨⟨0, 0⟩, ⟨0, 0, 0, 0⟩, []⟩⟩, ?_, by simp⟩
    simpa [List.mapM_nil, pure, Except.pure, List.map_nil] using h
  | cons a l ih =>
    intro ys h
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := htu_bind_ok h
    obtain ⟨bs, hbs, h⟩ := htu_bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    subst hys
    obtain ⟨g, hgm, hgf⟩ := ih hbs
    refine ⟨fun x => if x = a then b else g x, ?_, ?_⟩
    · rw [List.map_cons, ite_eq_left rfl, hgm, List.map_congr_left (f := g)
        (g := fun x => if x = a then b else g x) (l := l) (fun x hx => by
          by_cases hxa : x = a
          · subst hxa
            have hgx : g x = b := Except.ok.inj ((hgf x hx).symm.trans hfb)
            rw [ite_eq_left (rfl : x = x), hgx]
          · rw [ite_eq_right hxa])]
    · intro x hx
      by_cases hxa : x = a
      · subst hxa
        simpa using hfb
      · show f x = Except.ok (if x = a then b else g x)
        rw [ite_eq_right hxa]
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd rfl hxa
        · exact hgf x hx'

private theorem htu_bundleLayout_top {recur base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {margin gap : Int} {b : Bundle} {l : BundleLayout}
    (hfib : bundleLayout recur base inp o margin gap b = .ok l) :
    ∃ top : ModelBox, l.top = top ∧ top ∈ inp.boxes ∧ inp.boxes[b.target]? = some top := by
  unfold bundleLayout at hfib
  cases hb : inp.boxes[b.target]? with
  | none =>
    rw [hb] at hfib
    simp at hfib
  | some top =>
    rw [hb] at hfib
    simp only [bind, Except.bind] at hfib
    obtain ⟨part, hpart, hfib⟩ := htu_bind_ok hfib
    obtain ⟨notes, hnotes, hfib⟩ := htu_bind_ok hfib
    have hl : l = ⟨top, b, part, notes, _⟩ := (Except.ok.inj hfib).symm
    have htop : l.top = top := by rw [hl]
    have htopmem : top ∈ inp.boxes := by
      obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp hb
      rw [← heq]
      exact List.getElem_mem hi
    exact ⟨top, htop, htopmem, rfl⟩

private theorem htu_bundleLayout_bundle {recur base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {margin gap : Int} {b : Bundle} {l : BundleLayout}
    (hfib : bundleLayout recur base inp o margin gap b = .ok l) :
    l.bundle = b := by
  unfold bundleLayout at hfib
  cases hb : inp.boxes[b.target]? with
  | none =>
    rw [hb] at hfib
    simp at hfib
  | some top =>
    rw [hb] at hfib
    simp only [bind, Except.bind] at hfib
    obtain ⟨part, hpart, hfib⟩ := htu_bind_ok hfib
    obtain ⟨notes, hnotes, hfib⟩ := htu_bind_ok hfib
    have hl : l = ⟨top, b, part, notes, _⟩ := (Except.ok.inj hfib).symm
    rw [hl]

private theorem htu_fold_targets_nodup {boxes : List ModelBox} {atts : List Attach} :
    ∀ (acc : List Bundle), (acc.map Bundle.target).Nodup →
      ∀ (as : List Attach),
        ((List.foldl (fun acc a =>
            if isNested boxes atts a.target || acc.any (·.target == a.target) then acc
            else acc ++ [⟨a.target, atts.filter (·.target == a.target)⟩])
            acc as).map Bundle.target).Nodup := by
  intro acc hnd as
  induction as generalizing acc with
  | nil => exact hnd
  | cons a as ih =>
    rw [List.foldl_cons]
    by_cases hcb : (isNested boxes atts a.target || acc.any (·.target == a.target)) = true
    · rw [ite_eq_left hcb]
      exact ih acc hnd
    · rw [ite_eq_right hcb]
      have hnd' : ((acc ++ [⟨a.target, atts.filter (·.target == a.target)⟩] : List Bundle).map
          Bundle.target).Nodup := by
        rw [List.map_append]
        refine List.nodup_append.mpr ⟨hnd, ?_, ?_⟩
        · simp
        · intro x hx y hy hne
          rw [List.mem_map] at hx hy
          obtain ⟨b, hbx, hbt⟩ := hx
          obtain ⟨c, hc, hct⟩ := hy
          have hcnew : c = ⟨a.target, atts.filter (·.target == a.target)⟩ :=
            List.mem_singleton.mp hc
          have hyt : y = a.target := by rw [← hct, hcnew]
          have hnot : ¬ (a.target ∈ acc.map Bundle.target) := by
            intro hm
            obtain ⟨eb, ebx, ebt⟩ := List.mem_map.mp hm
            have hany : acc.any (·.target == a.target) = true := by
              rw [List.any_eq_true]
              exact ⟨eb, ebx, beq_iff_eq.mpr ebt⟩
            exact hcb (by simp [hany])
          have hxt : x ≠ a.target := by
            intro heq
            refine hnot (List.mem_map.mpr ⟨b, hbx, ?_⟩)
            rw [hbt]
            exact heq
          exact hxt (hne.trans hyt)
      exact ih _ hnd'

private theorem htu_bundles_targets_nodup {boxes : List ModelBox} {atts : List Attach} :
    ((bundlesOf boxes atts).map Bundle.target).Nodup := by
  unfold bundlesOf
  exact htu_fold_targets_nodup [] (by simp) atts

private theorem htu_fold_mem {boxes : List ModelBox} {atts : List Attach} :
    ∀ (acc : List Bundle) (as : List Attach) (b : Bundle),
      b ∈ List.foldl (fun acc a =>
        if isNested boxes atts a.target || acc.any (·.target == a.target) then acc
        else acc ++ [⟨a.target, atts.filter (·.target == a.target)⟩])
        acc as →
      b ∈ acc ∨ ∃ t, b = ⟨t, atts.filter (·.target == t)⟩ := by
  intro acc as
  induction as generalizing acc with
  | nil => intro b hb; exact Or.inl hb
  | cons a as ih =>
    intro b hb
    rw [List.foldl_cons] at hb
    by_cases hc : (isNested boxes atts a.target || acc.any (·.target == a.target)) = true
    · rw [ite_eq_left hc] at hb
      exact ih acc b hb
    · rw [ite_eq_right hc] at hb
      rcases ih (acc ++ [⟨a.target, atts.filter (·.target == a.target)⟩]) b hb with hmem | hext
      · rcases List.mem_append.mp hmem with hm | hm
        · exact Or.inl hm
        · exact Or.inr ⟨a.target, List.mem_singleton.mp hm⟩
      · exact Or.inr hext

private theorem htu_bundle_eq_of_mem {boxes : List ModelBox} {atts : List Attach}
    {b₁ b₂ : Bundle} (hb₁ : b₁ ∈ bundlesOf boxes atts) (hb₂ : b₂ ∈ bundlesOf boxes atts)
    (h : b₁.target = b₂.target) : b₁ = b₂ := by
  unfold bundlesOf at hb₁ hb₂
  rcases htu_fold_mem [] atts b₁ hb₁ with him₁ | ⟨t₁, hb₁'⟩
  · exact absurd him₁ (by simp)
  rcases htu_fold_mem [] atts b₂ hb₂ with him₂ | ⟨t₂, hb₂'⟩
  · exact absurd him₂ (by simp)
  have ht : t₁ = t₂ := by
    have e1 : b₁.target = t₁ := by rw [hb₁']
    have e2 : b₂.target = t₂ := by rw [hb₂']
    rw [e1, e2] at h
    exact h
  rw [hb₁', hb₂', ht]

private theorem htu_layouts_map_bundle {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    e.layouts.map BundleLayout.bundle = e.bundles := by
  obtain ⟨g, hgm, hgf⟩ := htu_mapM_exists_map _ e.layouts_eq
  have hbundle : ∀ b ∈ e.bundles, (g b).bundle = b := fun b hb => htu_bundleLayout_bundle (hgf b hb)
  rw [hgm]
  simp only [List.map_map]
  rw [List.map_congr_left (f := BundleLayout.bundle ∘ g) (g := id) (l := e.bundles)
    (fun b hb => by show BundleLayout.bundle (g b) = b; exact hbundle b hb)]
  exact List.map_id e.bundles

private theorem htu_map_nodup_of_injOn {α β : Type} (f : α → β) {l : List α}
    (h : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2 (fun a ha b hb hab => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨a, ha, hfa⟩ := hmem
    have hax : a = x := hinj a (List.mem_cons_of_mem _ ha) x List.mem_cons_self hfa
    subst hax
    exact h.1 ha

private theorem htu_nodup_of_map_nodup {α β : Type} (f : α → β) {l : List α}
    (h : (l.map f).Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    refine ⟨?_, ih h.2 (fun a ha b hb hab => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)⟩
    intro hmem
    exact h.1 (List.mem_map.mpr ⟨x, hmem, rfl⟩)

private theorem htu_bundles_nodup {boxes : List ModelBox} {atts : List Attach} :
    (bundlesOf boxes atts).Nodup := by
  exact htu_nodup_of_map_nodup Bundle.target htu_bundles_targets_nodup
    (fun a ha b hb h => htu_bundle_eq_of_mem ha hb h)

private theorem htu_layout_eq_of_top_id {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) {l₁ l₂ : BundleLayout}
    (hi : l₁ ∈ e.layouts) (hj : l₂ ∈ e.layouts)
    (hid : l₁.top.id = l₂.top.id) : l₁ = l₂ := by
  obtain ⟨b₁, hb₁, hfib₁⟩ := htu_mapM_mem _ _ e.layouts_eq l₁ hi
  obtain ⟨b₂, hb₂, hfib₂⟩ := htu_mapM_mem _ _ e.layouts_eq l₂ hj
  obtain ⟨top₁, htop₁, _, hb₁get⟩ := htu_bundleLayout_top hfib₁
  obtain ⟨top₂, htop₂, _, hb₂get⟩ := htu_bundleLayout_top hfib₂
  have hnd : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have htopid : top₁.id = top₂.id := by
    have e1 : l₁.top.id = top₁.id := by rw [htop₁]
    have e2 : l₂.top.id = top₂.id := by rw [htop₂]
    rw [e1, e2] at hid
    exact hid
  -- work in the id list: (boxes.map (·.id))[bᵢ.target]? = some topᵢ.id
  have htarget : b₁.target = b₂.target := by
    obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hb₁get
    obtain ⟨h2, _⟩ := List.getElem?_eq_some_iff.mp hb₂get
    have b1' : b₁.target < (inp.boxes.map (·.id)).length := by rw [List.length_map]; exact h1
    have b2' : b₂.target < (inp.boxes.map (·.id)).length := by rw [List.length_map]; exact h2
    have heq : (inp.boxes.map (·.id))[b₁.target]? = (inp.boxes.map (·.id))[b₂.target]? := by
      simp only [List.getElem?_map, hb₁get, hb₂get, Option.map_some]
      rw [htopid]
    exact (hnd.getElem?_inj b1').mp heq
  have hb₁' : b₁ ∈ bundlesOf inp.boxes e.atts := by rw [← e.bundles_eq]; exact hb₁
  have hb₂' : b₂ ∈ bundlesOf inp.boxes e.atts := by rw [← e.bundles_eq]; exact hb₂
  have hb_eq : b₁ = b₂ := htu_bundle_eq_of_mem hb₁' hb₂' htarget
  have hl : l₁ = l₂ := by
    rw [← hb_eq] at hfib₂
    exact Except.ok.inj (hfib₁.symm.trans hfib₂)
  exact hl

private theorem htu_layouts_nodup {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : e.layouts.Nodup := by
  obtain ⟨g, hgm, hgf⟩ := htu_mapM_exists_map _ e.layouts_eq
  rw [hgm, e.bundles_eq, e.atts_eq]
  apply htu_map_nodup_of_injOn _ htu_bundles_nodup
  intro a ha b hb hab
  have ha' : a ∈ e.bundles := by rw [e.bundles_eq, e.atts_eq]; exact ha
  have hb' : b ∈ e.bundles := by rw [e.bundles_eq, e.atts_eq]; exact hb
  have h1 : (g a).bundle = a := htu_bundleLayout_bundle (hgf a ha')
  have h2 : (g b).bundle = b := htu_bundleLayout_bundle (hgf b hb')
  rw [← h1, ← h2, hab]

theorem notesC8aTopNodup_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) :
    NotesC8aTopNodup e := by
  unfold NotesC8aTopNodup
  apply htu_map_nodup_of_injOn (·.top.id) (htu_layouts_nodup e)
  intro a ha b hb h
  exact htu_layout_eq_of_top_id e hwf ha hb h

/-- C6 bridge: the eight open C6 conjuncts plus the three mirror primitives
that yield the two exclusivities with local nodup. -/
def Nc68C6BridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC6AncC e ∧ NotesC6AncF e ∧ NotesC6FlagsKept e ∧ NotesC6FlagsFrag e ∧
    NotesC6KeptFrag e ∧ NotesC6FragContracted e ∧ NotesC6FragOther e ∧
    NotesC6RouterClear e ∧ NotesBaseContract e ∧ NotesBaseFrag e ∧ NotesFragRoots e

/-- C8a geometry premises beyond the contraction fold and base box mirror. -/
def Nc68C8aBridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesBaseContract e ∧ NotesC8aFragRole e ∧
    NotesC8aFragFound e ∧ NotesC8aClear e ∧ NotesC8aFragDisj e ∧
    NotesC8aSceneAnc e ∧ NotesC8aEnv e ∧ NotesC8aEnvDisj e ∧
    (∀ cg ∈ e.contracted.scene.boxes, ∃ fb ∈ (e.layouts.foldl contractOne inp).boxes,
      fb.id = cg.id ∧ cg.role = fb.role.id)

/-- C8a geometry (true role form) from the bridge and local well-formedness. -/
theorem nc68C8aGeomT_of_bridgeW
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hW : Nc68C8aBridgeW e) :
    NotesC8aGeomT e := by
  obtain ⟨hbase, hfr, hff, hclr, hfd, hsa, henv, henvd, hmir⟩ := hW
  have hnd : (inp.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hfold : NotesC8aFold e := contractFold_parentTransfer inp e.layouts hnd
  have hlen : NotesC8aLen e := by
    have hids := congrArg List.length hbase.1
    simp only [List.length_map] at hids
    unfold NotesC8aLen
    rw [hids, e.contractedInput_eq]
    exact fold_length_le inp e.layouts
  have hcs : NotesC8aContractScene e := by
    have h := notesContractedScene_parentTransfer e hnd hbase
    rw [e.contractedInput_eq] at h
    exact h
  have hcrT := notesC8aContractRoleT_holds e hnd hmir
  have htop := notesC8aTopNodup_holds e hwf
  exact ⟨htop, hfold, hlen, hcs, hcrT, hfr, hff, hclr, hfd, hsa, henv, henvd⟩

/-- C6 geometry from the bridge and local well-formedness. -/
theorem nc68C6Geom_of_bridgeW
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hW : Nc68C6BridgeW e) :
    NotesC6Geom e := by
  obtain ⟨hAncC, hAncF, hFK, hFF, hKF, hFC, hFO, hRC, hBC, hBF, hRoots⟩ := hW
  have hnd : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hCM := notesContractMirror_holds e hBC
  have hFRM := notesFragMirror_holds e hBF hRoots hnd
  have hExclC := ngfC6BoxExclC_holds e hCM hnd
  have hExclF := ngfC6BoxExclF_holds e hFRM hnd
  exact ⟨hAncC, hAncF, hFK, hFF, hExclC, hExclF, hKF, hFC, hFO, hRC⟩

/-- Guarded first-wins: on executed fragments with holding-rect and cross-absence,
the fragment lookup for each route-end id returns the holding fragment. This is the
true form the consumer (`notesFragBoxFirst_holds`) needs; the unconditional form
over arbitrary fragment lists is false (see header witness). -/
theorem nc68_fragFirstWins_of_unique
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {r : ModelRoute}
    (hSelf : ∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
      p.rect sb.id = some (shiftRect p.dx p.dy sb.rect))
    (hCross : ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
      ∀ sb ∈ p.scene.boxes, q.rect sb.id = none) :
    notesFragFirstWins e.fragments r := by
  have hFM := notesFirstMatch_holds e hSelf hCross
  intro id hid p hp b hmem hbid
  have h := hFM p hp b hmem
  rw [hbid] at h
  exact h

