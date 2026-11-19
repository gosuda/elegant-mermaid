import Elegant.Chart.TreemapClearanceFacts
import Elegant.Chart.TreemapContainmentFacts

namespace Elegant.Treemap.C8b

open Elegant.Treemap.TileForest

/-! Irreflexivity of the model-box ancestor relation.

`WellFormed` admits no parent cycles: `CanvasC1.parentDepth` measures every
real box id, and a parent sits exactly one level below its box, so no
`boxAncestors` walk can return to its own start id. -/

/-- Every element of a fuel-bounded ancestor list is a nonempty id: each
listed element is some found box's `parent` in the nonempty branch. -/
theorem boxAncestors_mem_ne (boxes : List ModelBox) :
    ∀ (k : Nat) (y z : String), z ∈ boxAncestors boxes k y → z ≠ "" := by
  intro k
  induction k with
  | zero =>
    intro y z hz
    have h0 : boxAncestors boxes 0 y = [] := rfl
    rw [h0] at hz
    exact absurd hz (by simp)
  | succ k ih =>
    intro y z hz
    rw [Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq
      boxes k y] at hz
    cases hfind : boxes.find? (fun b => b.id == y) with
    | none => simp [hfind] at hz
    | some c =>
      simp only [hfind] at hz
      by_cases hp : c.parent = ""
      · rw [ite_eq_left hp] at hz
        exact absurd hz (by simp)
      · rw [ite_eq_right hp] at hz
        obtain heq | hsub := List.mem_cons.mp hz
        · intro h0
          rw [heq] at h0
          exact hp h0
        · exact ih c.parent z hsub

/-- Any id listed in a fuel-bounded ancestor list has a depth profile, and
every profile of the nonempty start id is strictly larger: each listed
element is a parent, and `CanvasC1.parentDepth` drops one level per parent
edge. This is the acyclicity content of `WellFormed`. -/
theorem listed_ancestor_depth (m : Model) (hwf : WellFormed m)
    (nodes : List Node) (hsrc : nodes.map Node.source = m.boxes) :
    ∀ (k : Nat) (y x : String), y ≠ "" → x ∈ boxAncestors m.boxes k y →
      ∃ d, CanvasC1.DepthProfile nodes x d ∧
        ∀ d₀, CanvasC1.DepthProfile nodes y d₀ → d < d₀ := by
  intro k
  induction k with
  | zero =>
    intro y x _ hx
    have h0 : boxAncestors m.boxes 0 y = [] := rfl
    rw [h0] at hx
    exact absurd hx (by simp)
  | succ k ih =>
    intro y x hy hx
    have hnodup : (nodes.map (fun n => n.source.id)).Nodup :=
      CanvasC1.source_ids_nodup m hwf nodes hsrc
    rw [Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq
      m.boxes k y] at hx
    cases hfind : m.boxes.find? (fun b => b.id == y) with
    | none => simp [hfind] at hx
    | some c =>
      simp only [hfind] at hx
      have hcmem : c ∈ m.boxes := List.mem_of_find?_eq_some hfind
      have hcid : c.id = y := by
        have hpred := List.find?_some hfind
        simpa using hpred
      have hprof := CanvasC1.source_parent_depthProfile m hwf nodes hsrc c hcmem
      obtain ⟨dc, hdc⟩ := hprof
      by_cases hp : c.parent = ""
      · rw [ite_eq_left hp] at hx
        exact absurd hx (by simp)
      · rw [ite_eq_right hp] at hx
        have hyid : c.id ≠ "" := by rw [hcid]; exact hy
        obtain ⟨n, hn, hns⟩ : ∃ n ∈ nodes, n.source = c := by
          have hc' : c ∈ nodes.map Node.source := by
            rw [hsrc]; exact hcmem
          obtain ⟨n, hn, hns⟩ := List.mem_map.mp hc'
          exact ⟨n, hn, hns⟩
        have hlookup := CanvasC1.find_source_id_of_mem nodes hnodup n hn
        have hstep := CanvasC1.depthProfile_step nodes n
          (show n.source.id ≠ "" by rw [hns]; exact hyid) hlookup dc (by rw [hns]; exact hdc)
        rw [hns] at hstep
        rw [hcid] at hstep
        have hyprofile : ∀ d₀, CanvasC1.DepthProfile nodes y d₀ → d₀ = dc + 1 :=
          fun d₀ hd₀ =>
            CanvasC1.depthProfile_unique nodes y d₀ (dc + 1) hd₀ hstep
        obtain heq | hsub := List.mem_cons.mp hx
        · subst heq
          exact ⟨dc, hdc, fun d₀ hd₀ => by
            have := hyprofile d₀ hd₀; omega⟩
        · obtain ⟨d, hdx, hbnd⟩ := ih c.parent x hp hsub
          exact ⟨d, hdx, fun d₀ hd₀ => by
            have h1 := hyprofile d₀ hd₀
            have h2 := hbnd dc hdc
            omega⟩

/-- The ancestor relation is irreflexive: well-formedness makes every parent
chain terminate, so `boxAncestors` never lists the id itself. -/
theorem boxAncestors_irrefl (m : Model) (hwf : WellFormed m) (x : String) :
    x ∉ boxAncestors m.boxes m.boxes.length x := by
  intro hmem
  have hne := boxAncestors_mem_ne m.boxes m.boxes.length x x hmem
  obtain ⟨nodes, hsrc⟩ : ∃ nodes : List Node, nodes.map Node.source = m.boxes :=
    ⟨Elegant.Treemap.initialNodes m, Elegant.Treemap.CanvasC1.initialNodes_source m⟩
  obtain ⟨d, hd, hbound⟩ :=
    listed_ancestor_depth m hwf nodes hsrc m.boxes.length x x hne hmem
  exact absurd (hbound d hd) (by omega)
