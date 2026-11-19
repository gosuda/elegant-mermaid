import Elegant.Layered.CoordGraph

/-!
Shape of the compound source graph: unique border-`-2` anchor paths and no title-copy border.
-/

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

theorem cgShape_of_nodes_eq {g h : Graph} (he : g.nodes = h.nodes) (hs : CgShape g) :
    CgShape h := by
  unfold CgShape at *
  rw [← he]
  exact hs

theorem sizedNodes_border {P : Params} {lines : List (List Measure.Line)} {ns : List Node}
    (h : sizedNodes P lines = .ok ns) : ∀ n ∈ ns, n.border = 0 := by
  unfold sizedNodes at h
  have hm := Metadata.mapM_projection (fun q : List Measure.Line × Nat => sizedNode P q.2 q.1)
    (fun _ => (0 : Int)) (fun n : Node => n.border) (by
      intro a b hab
      unfold sizedNode at hab
      obtain ⟨size, _, hab⟩ := bind_ok' hab
      have hab := Except.ok.inj hab
      subst hab
      rfl) h
  intro n hn
  have : n.border ∈ ns.map (·.border) := List.mem_map_of_mem hn
  rw [hm] at this
  obtain ⟨_, _, hz⟩ := List.mem_map.mp this
  exact hz.symm

theorem components_nodup (g : Graph) : ∀ comp ∈ components g, comp.Nodup := by
  intro comp hc
  unfold components at hc
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
  exact List.Nodup.sublist List.filter_sublist List.nodup_range

theorem componentGraph_shape {g : Graph} {comp : List Nat} (hnd : comp.Nodup)
    (hs : CgShape g) : CgShape (componentGraph g comp) := by
  have hdef : ∀ v, g.nodes.getD v default = default ∨ ∃ n, g.nodes[v]? = some n ∧
      g.nodes.getD v default = n := by
    intro v
    cases hv : g.nodes[v]? with
    | none => left; simp [List.getD_eq_getElem?_getD, hv]
    | some n => right; exact ⟨n, rfl, by simp [List.getD_eq_getElem?_getD, hv]⟩
  have hdb : (default : Node).border = 0 := rfl
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb h1 h2 hp
    simp only [componentGraph, List.getElem?_map] at ha hb
    cases hca : comp[a]? with
    | none => simp [hca] at ha
    | some va =>
      cases hcb : comp[b]? with
      | none => simp [hcb] at hb
      | some vb =>
        simp only [hca, Option.map_some, Option.some.injEq] at ha
        simp only [hcb, Option.map_some, Option.some.injEq] at hb
        subst ha
        subst hb
        rcases hdef va with hda | ⟨n1, hn1, hd1⟩
        · rw [hda] at h1; rw [hdb] at h1; omega
        · rcases hdef vb with hdb' | ⟨n2, hn2, hd2⟩
          · rw [hdb'] at h2; rw [hdb] at h2; omega
          · rw [hd1] at h1 hp
            rw [hd2] at h2 hp
            have hv := hs.1 va vb n1 n2 hn1 hn2 h1 h2 hp
            subst hv
            exact nodup_map_inj_aux (fun x => x) (by simpa using hnd) hca hcb rfl
  · intro n hn
    simp only [componentGraph, List.mem_map] at hn
    obtain ⟨v, _, rfl⟩ := hn
    rcases hdef v with hd | ⟨n1, hn1, hd1⟩
    · rw [hd, hdb]; omega
    · rw [hd1]
      exact hs.2 n1 (List.mem_of_getElem? hn1)

theorem componentCandidate_nodes (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes = (componentGraph g comp).nodes := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

theorem componentCandidate_shape {g : Graph} {comp : List Nat} (hnd : comp.Nodup)
    (hs : CgShape g) (index : Nat) : CgShape (componentCandidate g comp index) :=
  cgShape_of_nodes_eq (componentCandidate_nodes g comp index).symm
    (componentGraph_shape hnd hs)

theorem orientNode_border (d : Direction) (n : Node) : (orientNode d n).border = n.border := by
  unfold orientNode
  split <;> rfl

def markOne (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int))
    (q : Node × Nat) : Node :=
  match boxes[q.2]? with
  | none => q.1
  | some box =>
    if box.role == .group then
      let title := titles.getD q.2 (0, 0)
      { q.1 with
        clusterPath := Compound.path boxes box ++ [q.2]
        border := -2
        w := title.1
        h := if q.1.loopExtent == 0 then title.2 + pad else max (title.2 + pad) q.1.h }
    else { q.1 with clusterPath := Compound.path boxes box }

def markExtras (boxes : List ModelBox) : List Node :=
  boxes.zipIdx.filterMap fun q =>
    if q.1.role == .group then
      some {
        decl := q.2, w := 0, h := 0
        clusterPath := Compound.path boxes q.1 ++ [q.2], border := 2 }
    else none

theorem markNodes_eq (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int))
    (nodes : List Node) :
    Compound.markNodes boxes pad titles nodes =
      nodes.zipIdx.map (markOne boxes pad titles) ++ markExtras boxes := rfl

theorem markOne_border {boxes : List ModelBox} {pad : Int} {titles : List (Int × Int)}
    {n : Node} {i : Nat} (hb : n.border = 0) :
    (markOne boxes pad titles (n, i)).border ≠ 3 ∧
      ((markOne boxes pad titles (n, i)).border = -2 →
        ∃ path : List Nat, (markOne boxes pad titles (n, i)).clusterPath = path ++ [i]) := by
  unfold markOne
  dsimp only
  split
  · exact ⟨by omega, fun h => by omega⟩
  · split
    · exact ⟨by show (-2 : Int) ≠ 3; decide, fun _ => ⟨_, rfl⟩⟩
    · exact ⟨by simp [hb], fun h => by simp [hb] at h⟩

theorem markExtras_border {boxes : List ModelBox} :
    ∀ n ∈ markExtras boxes, n.border = 2 := by
  intro n hn
  unfold markExtras at hn
  obtain ⟨q, _, hq⟩ := List.mem_filterMap.mp hn
  split at hq
  · simp only [Option.some.injEq] at hq
    subst hq
    rfl
  · simp at hq

theorem markNodes_lookup {boxes : List ModelBox} {pad : Int} {titles : List (Int × Int)}
    {nodes : List Node} (hb : ∀ n ∈ nodes, n.border = 0) {v : Nat} {nd : Node}
    (h : (Compound.markNodes boxes pad titles nodes)[v]? = some nd) :
    nd.border ≠ 3 ∧ (nd.border = -2 → ∃ path : List Nat, nd.clusterPath = path ++ [v]) := by
  rw [markNodes_eq] at h
  by_cases hv : v < (nodes.zipIdx.map (markOne boxes pad titles)).length
  · rw [List.getElem?_append_left hv] at h
    simp only [List.getElem?_map, List.getElem?_zipIdx] at h
    cases hn : nodes[v]? with
    | none => simp [hn] at h
    | some n =>
      simp only [hn, Option.map_some, Option.some.injEq] at h
      subst h
      simpa using markOne_border (boxes := boxes) (pad := pad) (titles := titles) (i := 0 + v)
        (hb n (List.mem_of_getElem? hn))
  · rw [List.getElem?_append_right (by omega)] at h
    have := markExtras_border nd (List.mem_of_getElem? h)
    exact ⟨by omega, fun h2 => by omega⟩

theorem prepare_shape {boxes : List ModelBox} {pad : Int} {titles : List (Int × Int)}
    {g : Graph} (hb : ∀ n ∈ g.nodes, n.border = 0) :
    CgShape (Compound.prepare boxes pad titles g) := by
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb' h1 h2 hp
    obtain ⟨_, pa⟩ := markNodes_lookup (boxes := boxes) (pad := pad) (titles := titles) hb ha
    obtain ⟨_, pb⟩ := markNodes_lookup (boxes := boxes) (pad := pad) (titles := titles) hb hb'
    obtain ⟨p1, hp1⟩ := pa h1
    obtain ⟨p2, hp2⟩ := pb h2
    rw [hp1, hp2] at hp
    have := congrArg List.getLast? hp
    simp at this
    exact this
  · intro n hn
    obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hn
    exact (markNodes_lookup (boxes := boxes) (pad := pad) (titles := titles) hb hv).1

theorem measuredGraph_shape {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (h : measuredGraph P inp o lines = .ok g) : CgShape g := by
  unfold measuredGraph at h
  obtain ⟨ns, hns, h⟩ := bind_ok' h
  obtain ⟨edges, hedges, h⟩ := bind_ok' h
  obtain ⟨m, hm, h⟩ := bind_ok' h
  obtain ⟨labels, hlabels, h⟩ := bind_ok' h
  obtain ⟨nodes2, hnodes2, h⟩ := bind_ok' h
  have h : (Except.ok _ : Except LayoutError Graph) = Except.ok g := h
  have hg := Except.ok.inj h
  subst hg
  apply prepare_shape
  show ∀ n ∈ nodes2, n.border = 0
  have hb := sizedNodes_border hns
  have hproj := Metadata.mapM_projection _ (fun q : Node × Nat => q.1.border)
    (fun n : Node => n.border) ?_ hnodes2
  · intro n hn
    have : n.border ∈ nodes2.map (·.border) := List.mem_map_of_mem hn
    rw [hproj] at this
    obtain ⟨q, hq, hqb⟩ := List.mem_map.mp this
    obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hq
    rw [List.getElem?_zipIdx] at hv
    cases hnv : ns[v]? with
    | none => simp [List.getElem?_map, hnv] at hv
    | some x =>
      simp only [List.getElem?_map, hnv, Option.map_some, Option.some.injEq] at hv
      rw [← hqb, ← hv]
      simp only [orientNode_border]
      exact hb x (List.mem_of_getElem? hnv)
  · intro q b hq
    dsimp only at hq
    simp only [bind, Except.bind, pure, Except.pure] at hq
    split at hq
    · simp at hq
    · split at hq <;> (try split at hq) <;> (try split at hq) <;> (try split at hq) <;>
        first
        | (have h2 := Except.ok.inj hq; subst h2; simp [orientNode_border]; done)
        | (simp [throw, throwThe, MonadExceptOf.throw] at hq; done)

end PipelineImpl
end Layered
end Elegant
