import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.Pipeline
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactC8aSpansProof
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactForeignNonGroupSpansProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactBorderChainXAlignedProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.RecursiveBLiftsB
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Exact flat C8a core: `FlatC8aB (layoutX exactIds)`.

Plain chain (`ForeignSpansFacts.lean`): `flatC8a_of_span_seams` over
`foreignBorderSpansSeparated`, `foreignNonGroupSpansClear`,
`bracketInsidePremises`; execution form `flatC8a_executed` composes
`layout_c8a_executed` with `frameClearanceSeam_holds` + `foreignSpansClear_of_run`.

Exact replay over `SceneExecutionX`: the per-run span facts come from the
XB_/XN_ seams (`XB_foreignBorderSpansSeparated_holds`,
`XN_foreignNonGroupSpansClear_holds`) with the three closed run facts from
`ExactBorderSpanRunFactsProof` and the closed chain bridge; plain-node
disjointness is `XS_C8a_PositionsDisjoint_of_run`. The executed case split
(same-component frame rectangles vs disjoint packed boxes) mirrors
`layout_c8a_executed` with the `X` execution API. The two `XSc8a_` residuals
(`AnchorCover`, `MemberBounds`, owned by another worker) are not needed here:
the XB_/XN_ leaves are taken as premises directly. -/

local instance xfc8aInhabitedModelBox : Inhabited ModelBox := ⟨{ id := "" }⟩

/-- File-unique copy of `getElem_unique_of_nodup_map`: id-injective lookup. -/
private theorem xfc8a_getElem_unique_of_nodup_map {α : Type} {f : α → String} {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hid : f x = f y) :
    x = y := by
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy
  by_cases hij : i = j
  · subst hij
    exact hxi.symm.trans hyj
  · exfalso
    have hp := List.pairwise_iff_getElem.mp hnd
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have h := hp i j (by simpa using hi) (by simpa using hj) hlt
      exact h (by simp only [List.getElem_map, hxi, hyj, hid])
    · exact absurd heq hij
    · have h := hp j i (by simpa using hj) (by simpa using hi) hgt
      exact h (by simp only [List.getElem_map, hyj, hxi, ← hid])

/-- File-unique copy of `demote_id_parent`: fixed-size demotion keeps id/parent. -/
private theorem xfc8a_demote_id_parent (inp : Input) (b : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b).id = b.id ∧
      (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b).parent = b.parent := by
  split <;> simp

/-- File-unique copy: `Disjoint` survives `shiftRect`. -/
private theorem xfc8a_shiftRect_disjoint {a b : Rect} {dx dy : Int}
    (h : Disjoint a b) : Disjoint (shiftRect dx dy a) (shiftRect dx dy b) := by
  simp only [Disjoint, Rect.meetsInterior, shiftRect] at h ⊢
  omega

/-- File-unique copy: `Disjoint` survives `orientRect`. -/
private theorem xfc8a_orientRect_disjoint {a b : Rect} {d : Direction} {h : Int}
    (hm : Disjoint a b) : Disjoint (orientRect d h a) (orientRect d h b) := by
  intro hc
  exact hm (meetsInterior_of_orientRect hc)

/-- File-unique copy of `C8a_pack_box_dims`: packed box dims follow the items. -/
private theorem xfc8a_pack_box_dims {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    {k : Nat} (hk : k < out.boxes.length) (hik : k < items.length) :
    out.boxes[k].w = items[k].width ∧ out.boxes[k].h = items[k].height := by
  have hd := Pack.pack_dimensions h
  unfold Pack.dimensions at hd
  have h1 := congrArg (fun l => l[k]?) hd
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hik] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact h1

/-- File-unique copy: node lookup in a component candidate. -/
private theorem xfc8a_component_node_lookup {graph : Graph} {comp : List Nat} {cand : Nat}
    {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- File-unique copies: `zipIdx` preserves the first projection. -/
private theorem xfc8a_zipIdxAux_map_fst {α : Type} (l : List α) (n : Nat) :
    (l.zipIdx n).map Prod.fst = l := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, ih]
private theorem xfc8a_zipIdx_map_fst {α : Type} (l : List α) :
    l.zipIdx.map Prod.fst = l := by
  have h := xfc8a_zipIdxAux_map_fst l 0
  simpa only using h

/-- File-unique copy of `C8a_measuredGraphNodeX`: the exact graph node behind
one input box (declaration index and demoted ancestor path). -/
private theorem xfc8a_measuredGraphNodeX {exactIds : List String} {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {g0 g : Graph}
    (h0 : measuredGraph P inp o lines = .ok g0)
    (hg : exactGraph P exactIds inp o measured g0 = .ok g)
    (hlen : lines.length = inp.boxes.length)
    {eff : List ModelBox}
    (heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)
    {k : Nat} {s : ModelBox} {sg : ModelBox}
    (hk : inp.boxes[k]? = some s)
    (hsg : eff[k]? = some sg) :
    ∃ node : Node,
      g.nodes[k]? = some node ∧
      node.decl = k ∧
      ((node.border = -2 ∧ node.clusterPath = Compound.path eff sg ++ [k]) ∨
        (node.border = 0 ∧ node.clusterPath = Compound.path eff sg)) := by
  obtain ⟨nodes, edges, titles, hprepared, hnodesLen, hmeta⟩ :=
    measuredGraph_prepared_source h0
  have hkLen : k < lines.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hk).1
  have hkNodes : k < nodes.length := by rw [hnodesLen]; exact hkLen
  obtain ⟨hn0decl, hn0border⟩ := hmeta k nodes[k] (List.getElem?_eq_getElem hkNodes)
  rw [heff] at hsg
  by_cases hrole : sg.role = .group
  · have hrec := Compound.prepare_group_title_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles ⟨nodes, edges, P.slot⟩ hkNodes hsg hrole
    have hget0 : g0.nodes[k]? = some { nodes[k]'hkNodes with clusterPath := Compound.path (inp.boxes.map fun b => if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then { b with role := .node } else b) sg ++ [k], border := -2, w := (titles.getD k (0, 0)).1, h := if nodes[k].loopExtent == 0 then (titles.getD k (0, 0)).2 + P.clusterPad else max ((titles.getD k (0, 0)).2 + P.clusterPad) nodes[k].h } := by
      rw [hprepared]
      exact hrec
    obtain ⟨nd, hnd, hbEq, hcEq, hdeclEq⟩ := exactGraph_node_key hg hget0
    refine ⟨nd, hnd, ?_, Or.inl ⟨?_, ?_⟩⟩
    · simp [hdeclEq, hn0decl]
    · simp [hbEq]
    · simp [hcEq]
      rw [← heff]
  · have hrec := Compound.prepare_plain_node_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles ⟨nodes, edges, P.slot⟩ hkNodes hsg hrole
    have hget0 : g0.nodes[k]? = some { nodes[k]'hkNodes with clusterPath := Compound.path (inp.boxes.map fun b => if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then { b with role := .node } else b) sg } := by
      rw [hprepared]
      exact hrec
    obtain ⟨nd, hnd, hbEq, hcEq, hdeclEq⟩ := exactGraph_node_key hg hget0
    refine ⟨nd, hnd, ?_, Or.inr ⟨?_, ?_⟩⟩
    · simp [hdeclEq, hn0decl]
    · simp [hbEq, hn0border]
    · simp [hcEq]
      rw [← heff]

/-- File-unique copy of the ancestor-walk bridge: a strict model ancestor
index is an id of the dump ancestor walk. -/
private theorem xfc8a_compound_mem_dump_go {boxes : List ModelBox} {d : LayoutDump}
    (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
      ∃ (rect : Rect) (role : String),
        d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive)) :
    ∀ (fuel : Nat) (s : String) (i : Nat),
      i ∈ Compound.ancestors boxes (fuel + 1) s →
      i < boxes.length →
      (boxes[i]?.getD default).id ≠ s →
      (boxes[i]?.getD default).id ∈ LayoutDump.ancestors.go d fuel s := by
  intro fuel
  induction fuel with
  | zero =>
    intro s i hmem hi hne
    by_cases hs : s = ""
    · subst hs
      simp only [Compound.ancestors] at hmem
      exact absurd hmem (by simp)
    · have h3 : Compound.ancestors boxes (0 + 1) s =
          match boxes.findIdx? (fun box => box.id == s) with
        | none => []
        | some index =>
          match boxes[index]? with
          | none => []
          | some box => Compound.ancestors boxes 0 box.parent ++ [index] :=
        Compound.ancestors.eq_3 boxes s 0 hs
      rw [h3] at hmem
      cases hf : boxes.findIdx? (fun box => box.id == s) with
      | none => simp only [hf] at hmem; exact absurd hmem (by simp)
      | some j =>
        obtain ⟨hjb, hjid, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        simp only [hf] at hmem
        cases hb : boxes[j]? with
        | none => simp only [hb] at hmem; exact absurd hmem (by simp)
        | some bj =>
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          simp only [hb] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · simp only [Compound.ancestors] at hmem
            exact absurd hmem (by simp)
          · rw [hmem] at hne
            have hgd : boxes[j]?.getD default = bj := by rw [hb]; rfl
            have hjid2 : bj.id = s := by
              rw [← hbjEq]
              exact beq_iff_eq.mp hjid
            exact absurd ((congrArg (·.id) hgd).trans hjid2) hne
  | succ fuel ih =>
    intro s i hmem hi hne
    by_cases hs : s = ""
    · subst hs
      simp only [Compound.ancestors] at hmem
      exact absurd hmem (by simp)
    · have h3 : Compound.ancestors boxes (fuel + 1 + 1) s =
          match boxes.findIdx? (fun box => box.id == s) with
        | none => []
        | some index =>
          match boxes[index]? with
          | none => []
          | some box => Compound.ancestors boxes (fuel + 1) box.parent ++ [index] :=
        Compound.ancestors.eq_3 boxes s (fuel + 1) hs
      rw [h3] at hmem
      cases hf : boxes.findIdx? (fun box => box.id == s) with
      | none => simp only [hf] at hmem; exact absurd hmem (by simp)
      | some j =>
        obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        simp only [hf] at hmem
        cases hb : boxes[j]? with
        | none => simp only [hb] at hmem; exact absurd hmem (by simp)
        | some bj =>
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          simp only [hb] at hmem
          have hjids : bj.id = s := by
            rw [← hbjEq]
            exact beq_iff_eq.mp hjid
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · -- i sits in the parent chain: strip one dump-walk step
            obtain ⟨rect, role, excl, hbx⟩ : ∃ (rect : Rect) (role : String)
                (excl : Bool), d.box? s = some (Box.mk s role rect bj.parent excl) := by
              obtain ⟨rect, role, hx⟩ := himg j bj hb
              rw [hjids] at hx
              exact ⟨rect, role, bj.exclusive, hx⟩
            have hparNe : bj.parent ≠ "" := by
              intro hempty
              simp only [hempty, Compound.ancestors] at hmem
              exact absurd hmem (by simp)
            cases hd : d.box? s with
            | none => rw [hd] at hbx; exact absurd hbx (by simp)
            | some bx =>
              have hbxa : bx = Box.mk s role rect bj.parent excl :=
                Option.some.inj (hd.symm.trans hbx)
              have hbpar : bx.parent = bj.parent := by rw [hbxa]
              have hgo : LayoutDump.ancestors.go d (fuel + 1) s =
                  match d.box? s with
                  | none => []
                  | some bx' =>
                    if bx'.parent = "" then []
                    else bx'.parent :: LayoutDump.ancestors.go d fuel bx'.parent := rfl
              rw [hgo]
              simp only [hd, hbpar]
              split
              · rename_i hcond
                exact absurd hcond hparNe
              · by_cases hself : (boxes[i]?.getD default).id = bj.parent
                · rw [hself]
                  exact List.mem_cons_self
                · exact List.mem_cons.mpr (Or.inr (ih bj.parent i hmem hi hself))
          · rw [hmem] at hne
            have hgd : boxes[j]?.getD default = bj := by rw [hb]; rfl
            exact absurd ((congrArg (·.id) hgd).trans hjids) hne
/-- File-unique copy of the dump-ancestry transport. -/
private theorem xfc8a_anc_of_path_mem {boxes : List ModelBox} {d : LayoutDump}
    (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
      ∃ (rect : Rect) (role : String),
        d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive))
    (_hpre : ∀ bx : Box, bx ∈ d.boxes →
      ∃ b : ModelBox, b ∈ boxes ∧ b.id = bx.id ∧ b.parent = bx.parent)
    (_hid : ∀ (a b : ModelBox), a ∈ boxes → b ∈ boxes → a.id = b.id → a = b)
    (hlen : d.boxes.length = boxes.length)
    {t p : String} {idx : Nat} {s : String}
    (hroot : ∃ (role : String) (rect : Rect) (excl : Bool),
      d.box? t = some (Box.mk t role rect p excl))
    (hidx : idx < boxes.length)
    (hs : (boxes[idx]?.getD default).id = s)
    (hmem : idx ∈ Compound.ancestors boxes boxes.length p) :
    s ∈ d.ancestors t := by
  cases hlen' : boxes.length with
  | zero => rw [hlen'] at hidx; exact absurd hidx (by omega)
  | succ fuel =>
    obtain ⟨role, rect, excl, hroot⟩ := hroot
    rw [hlen'] at hmem
    have hlenSucc : d.boxes.length = fuel + 1 := by rw [hlen, hlen']
    have hgo : LayoutDump.ancestors.go d (fuel + 1) t =
        match d.box? t with
        | none => []
        | some bx =>
          if bx.parent = "" then [] else bx.parent :: LayoutDump.ancestors.go d fuel bx.parent :=
      rfl
    rw [LayoutDump.ancestors, hlenSucc, hgo]
    cases hd : d.box? t with
    | none => rw [hd] at hroot; exact absurd hroot (by simp)
    | some bx =>
      have hbxa : bx = Box.mk t role rect p excl :=
        Option.some.inj (hd.symm.trans hroot)
      have hbpar : bx.parent = p := by rw [hbxa]
      simp only [hbpar]
      split
      · rename_i hcond
        rw [hcond] at hmem
        simp only [Compound.ancestors] at hmem
        exact absurd hmem (by simp)
      · by_cases hself : (boxes[idx]?.getD default).id = p
        · rw [← hs, hself]
          exact List.mem_cons_self
        · have hgo2 := xfc8a_compound_mem_dump_go himg fuel p idx hmem hidx hself
          rw [hs] at hgo2
          exact List.mem_cons.mpr (Or.inr hgo2)

/-- File-unique copy: id-injective lookup for dump boxes. -/
private theorem xfc8a_eq_of_mem_idBox {boxes : List Box} (hnodup : (boxes.map (·.id)).Nodup)
    {a b : Box} (ha : a ∈ boxes) (hb : b ∈ boxes) (h : a.id = b.id) : a = b := by
  induction boxes generalizing a b with
  | nil => cases ha
  | cons c l ih =>
    rcases List.mem_cons.mp ha with rfl | hal
    · rcases List.mem_cons.mp hb with rfl | hbl
      · rfl
      · exact absurd (List.mem_map.mpr ⟨b, hbl, h.symm⟩) (List.nodup_cons.mp hnodup).1
    · rcases List.mem_cons.mp hb with rfl | hbl
      · exact absurd (List.mem_map.mpr ⟨a, hal, h⟩) (List.nodup_cons.mp hnodup).1
      · exact ih (List.nodup_cons.mp hnodup).2 hal hbl h

/-- File-unique copy of `X_part_packed_frame`: per-part containment and
packed rect values for exact runs. -/
private theorem xfc8a_part_packed_frame
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part)
    (hkLen : k < packed.boxes.length) :
    ∃ candidate run loops,
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph part.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
        packed.boxes[k].Contained (shiftRect packed.boxes[k].x packed.boxes[k].y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph part.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph part.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph part.1 candidate) run i)))) ∧
      (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
        execution.packedAcc.rects.getD key default =
          shiftRect packed.boxes[k].x packed.boxes[k].y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph part.1 candidate) run execution.measured
                loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph part.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph part.1 candidate) run i))) := by
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  obtain ⟨candidate, run, loops, _area, hrun, _hloops, hpartdef, hlookup⟩ :=
    part_frame_lookupX execution packed hpack hk hbox
  have hpartget := (List.getElem?_eq_some_iff.mp hk).2
  have hmapLen : k < (execution.componentsAcc.parts.map
      (fun part => Pack.Item.mk part.2.width part.2.height part.2.area)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨hw0, hh0⟩ := xfc8a_pack_box_dims hpack hkLen hmapLen
  have hitem : (execution.componentsAcc.parts.map
      (fun part => Pack.Item.mk part.2.width part.2.height part.2.area))[k] =
      Pack.Item.mk part.2.width part.2.height part.2.area := by
    rw [List.getElem_map, hpartget]
  have hwb : packed.boxes[k].w = part.2.width := by
    rw [hw0, hitem]
  have hhb : packed.boxes[k].h = part.2.height := by
    rw [hh0, hitem]
  have hwlink : part.2.width =
      (placeComponentExact execution.params
        (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops).width := by
    have hcongr := congrArg Part.width hpartdef
    simpa using hcongr
  have hhlink : part.2.height =
      (placeComponentExact execution.params
        (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops).height := by
    have hcongr := congrArg Part.height hpartdef
    simpa using hcongr
  refine ⟨candidate, run, loops, hrun, ?_, hlookup⟩
  intro i key hkey _
  have hi : i < (componentCandidate execution.graph part.1 candidate).nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hkey).1
  have hplaced : (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 candidate) run 0 execution.measured
      loops).rects[i]? =
    some (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 candidate) run execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 candidate) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 candidate) run i)) := by
    unfold placeComponentExact placeBoundsX
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
  have hmem := List.mem_of_getElem? hplaced
  have hb := placeComponentExact_rects_bounds execution.params
    (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops _
    hmem
  simp only [Rect.Contained, shiftRect] at hb ⊢
  rw [hwb, hhb, hwlink, hhlink]
  omega

-- (Main-theorem docstring re-attached below, before `flatC8aB_layoutX`.)
/-- The `X_` chain alignment and the `XB_` chain alignment are the same
statement over exact runs. -/
private theorem xfc8a_chainBridge {exactIds : List String}
    (h : X_ForeignBorderChainXAligned exactIds) :
    XB_ForeignBorderChainXAligned exactIds := h

/-- The exact group-vs-group seam from the leaf span facts: the three closed
run facts come from `ExactBorderSpanRunFactsProof`. -/
private theorem xfc8a_groups_of {exactIds : List String}
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (hchain : X_ForeignBorderChainXAligned exactIds) :
    XB_ForeignBorderSpansSeparated exactIds :=
  XB_foreignBorderSpansSeparated_holds exactIds hspans horder
    (xfc8a_chainBridge hchain) (XB_orderedIntervals_holds exactIds)
    (XB_topNonneg_holds exactIds) (XB_memberNonempty_holds exactIds)

/-- The exact non-group seam from the three `XN_` leaf facts. -/
private theorem xfc8a_others_of {exactIds : List String}
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignSide : XN_SideMarkerSpanAligned exactIds) :
    XN_ForeignNonGroupSpansClear exactIds :=
  XN_foreignNonGroupSpansClear_holds exactIds hbracket hplain halignSide

/-- Exact per-run foreign-span clearance from the `XB_`/`XN_` seams
(mirror of `foreignSpansClear_of_run` over `componentRunX`). -/
private theorem xfc8a_spansClear_of_run {exactIds : List String}
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hgX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hgroups : XB_ForeignBorderSpansSeparated exactIds)
    (hothers : XN_ForeignNonGroupSpansClear exactIds)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    ForeignSpansClear P (componentCandidate graph comp candidate) run := by
  intro u w uNode wNode hu hw hgroupU hne hpathW hpathU
  by_cases hgroupW : wNode.border = -2
  · exact frameRect_disjoint_of_hulls hu hgroupU hw hgroupW
      (hgroups hg0 hgX hlines hwf hfp hcomp hrun hu hw hgroupU hgroupW hne hpathW hpathU)
  · exact hothers hg0 hgX hlines hwf hfp hcomp hrun hu hw hgroupU hgroupW hne hpathW hpathU

/-- Exact C8a layout core over `SceneExecutionX` (mirror of
`layout_c8a_executed` with the `X` execution API). -/
private theorem xfc8a_layout_c8a_executedX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hspans : ∀ (part : List Nat × Part), part ∈ execution.componentsAcc.parts →
      ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
        componentRunX execution.params (exactDecls exactIds inp)
          (componentCandidate execution.graph part.1 candidate) execution.measured
          orderOptions = .ok run →
        ForeignSpansClear execution.params
          (componentCandidate execution.graph part.1 candidate) run)
    (hpos : XS_C8a_PositionsDisjoint exactIds) :
    Validator.C8a res.scene.layoutDump := by
  have _hfp := hfp
  have hboxesEq : res.scene.layoutDump.boxes = (inp.boxes.zipIdx.map fun q =>
      Box.mk q.1.id q.1.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD q.2 default)))
        q.1.parent q.1.exclusive) := by
    have h := execution.boxes_eq_mapX
    simp [Scene.layoutDump] at h ⊢
    exact h
  have hlen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    unfold boxLines at hl
    have h2 := (mapM_getElem? _ _ _ hl).1
    have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
    omega
  have hdlen : res.scene.layoutDump.boxes.length = inp.boxes.length := by
    rw [hboxesEq, List.length_map, List.length_zipIdx]
  have hpartsMap : execution.componentsAcc.parts.map (·.1) = components execution.graph := by
    exact (actual_components_parts_geometryX (by rfl) execution.components_eq).1
  have hidsNodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  let eff : List ModelBox := inp.boxes.map fun b =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
      { b with role := .node } else b
  have heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b := rfl
  have heffLen : eff.length = inp.boxes.length := by rw [heff, List.length_map]
  have heffGet : ∀ (k : Nat), eff[k]? =
      (inp.boxes[k]?).map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b := by
    intro k
    rw [heff, List.getElem?_map]
  have heffNodup : (eff.map (·.id)).Nodup := by
    have hcongr : eff.map (·.id) = inp.boxes.map (·.id) := by
      rw [heff, List.map_map]
      congr 1
      funext b
      exact (xfc8a_demote_id_parent inp b).1
    rw [hcongr]
    exact hidsNodup
  have heffUnique : ∀ (a b : ModelBox), a ∈ eff → b ∈ eff → a.id = b.id → a = b :=
    fun a b ha hb hid => xfc8a_getElem_unique_of_nodup_map heffNodup ha hb hid
  have hidsDumpNodup : (res.scene.layoutDump.boxes.map (·.id)).Nodup := by
    have hcongr : (res.scene.layoutDump.boxes.map (·.id)) = inp.boxes.map (·.id) := by
      rw [hboxesEq, List.map_map]
      simp only [Function.comp_def]
      have heq : (fun q : ModelBox × Nat => q.1.id) = (·.id) ∘ Prod.fst := by
        funext q
        rfl
      rw [heq, ← List.map_map, xfc8a_zipIdx_map_fst]
    rw [hcongr]
    exact hidsNodup
  have himg : ∀ (k : Nat) (b : ModelBox), eff[k]? = some b →
      ∃ (rect : Rect) (role : String),
        res.scene.layoutDump.box? b.id =
          some (Box.mk b.id role rect b.parent b.exclusive) := by
    intro k b hib
    cases hin : inp.boxes[k]? with
    | none => rw [heffGet, hin] at hib; exact absurd hib (by simp)
    | some orig =>
      rw [heffGet, hin] at hib
      have hbEq : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
          { orig with role := .node } else orig) = b := Option.some.inj hib
      subst hbEq
      obtain ⟨h1, h2⟩ := xfc8a_demote_id_parent inp orig
      have h3 : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
          { orig with role := .node } else orig).exclusive = orig.exclusive := by
        split <;> rfl
      rw [h1, h2, h3]
      have hmemZip : (orig, k) ∈ inp.boxes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hin
      have hmemBox : (Box.mk orig.id orig.role.id
          (shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (execution.packedAcc.rects.getD k default)))
          orig.parent orig.exclusive) ∈ res.scene.layoutDump.boxes := by
        rw [hboxesEq]
        exact List.mem_map.mpr ⟨(orig, k), hmemZip, rfl⟩
      have hbeq : ((Box.mk orig.id orig.role.id
            (shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH
                (execution.packedAcc.rects.getD k default)))
            orig.parent orig.exclusive).id == orig.id) = true := by
        simp
      have hsome : ((res.scene.layoutDump.boxes.find? fun b => b.id == orig.id).isSome =
          true) :=
        List.find?_isSome.mpr ⟨_, hmemBox, hbeq⟩
      cases hfind : res.scene.layoutDump.boxes.find? fun b => b.id == orig.id with
      | none => rw [hfind] at hsome; simp at hsome
      | some bx =>
        have hbxMem : bx ∈ res.scene.layoutDump.boxes :=
          List.mem_of_find?_eq_some hfind
        have hbxId : (bx.id == orig.id) = true := by
          have h := List.find?_some hfind
          simpa using h
        have hbxEq : (bx.id = orig.id) := beq_iff_eq.mp hbxId
        have huniq := xfc8a_eq_of_mem_idBox hidsDumpNodup hmemBox hbxMem
          (by rw [hbxEq])
        rw [← huniq] at hfind
        exact ⟨_, _, hfind⟩
  have hpre : ∀ bx : Box, bx ∈ res.scene.layoutDump.boxes →
      ∃ b : ModelBox, b ∈ eff ∧ b.id = bx.id ∧ b.parent = bx.parent := by
    intro bx hbx
    rw [hboxesEq] at hbx
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hbx
    have hk : inp.boxes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
    cases hin : inp.boxes[q.2]? with
    | none => rw [hin] at hk; exact absurd hk (by simp)
    | some s =>
      rw [hin] at hk
      have hsq : s = q.1 := Option.some.inj hk
      subst hsq
      have hkIn : eff[q.2]? = some
          (if inp.fixedSizes.any (fun fixed => fixed.1 == q.1.id) then
            { q.1 with role := .node } else q.1) := by
        rw [heffGet, hin, Option.map_some]
      refine ⟨_, List.mem_of_getElem? hkIn, ?_, ?_⟩
      · rw [(xfc8a_demote_id_parent inp q.1).1, ← hqeq]
      · rw [(xfc8a_demote_id_parent inp q.1).2, ← hqeq]
  have hdlen' : res.scene.layoutDump.boxes.length = eff.length := by
    rw [heffLen]
    exact hdlen
  intro g hgMem _ b hbMem hbId hgAnc hbAnc
  obtain ⟨sg, bi, hbi, hgeq⟩ : ∃ (s : ModelBox) (k : Nat), inp.boxes[k]? = some s ∧
      g = Box.mk s.id s.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD k default)))
        s.parent s.exclusive := by
    rw [hboxesEq] at hgMem
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hgMem
    exact ⟨q.1, q.2, List.mem_zipIdx_iff_getElem?.mp hq, hqeq.symm⟩
  obtain ⟨sb, bk, hbk, hbeq⟩ : ∃ (s : ModelBox) (k : Nat), inp.boxes[k]? = some s ∧
      b = Box.mk s.id s.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD k default)))
        s.parent s.exclusive := by
    rw [hboxesEq] at hbMem
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hbMem
    exact ⟨q.1, q.2, List.mem_zipIdx_iff_getElem?.mp hq, hqeq.symm⟩
  have hgId : g.id = sg.id := by rw [hgeq]
  have hbIdEq : b.id = sb.id := by rw [hbeq]
  have hgRect : g.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD bi default)) := by rw [hgeq]
  have hbRect : b.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD bk default)) := by rw [hbeq]
  have hbid : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hbi).1
  have hbkBound : bk < inp.boxes.length := (List.getElem?_eq_some_iff.mp hbk).1
  have hbik : bi ≠ bk := by
    intro heq
    rw [heq] at hbi
    exact hbId (by rw [hbIdEq, hgId, ← Option.some.inj (hbi.symm.trans hbk)])
  rw [hgId, hbIdEq] at hgAnc hbAnc
  have heffIdOf : ∀ (k : Nat) (s : ModelBox), inp.boxes[k]? = some s →
      (eff[k]?.getD default).id = s.id ∧ (eff[k]?.getD default).parent = s.parent := by
    intro k s hk
    rw [heffGet, hk]
    simp only [Option.map_some, Option.getD_some]
    exact xfc8a_demote_id_parent inp s
  have hrootT1 : ∃ (role : String) (rect : Rect) (excl : Bool),
      res.scene.layoutDump.box? sb.id =
        some (Box.mk sb.id role rect sb.parent excl) := by
    obtain ⟨rect, role, hx⟩ := himg bk
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
        { sb with role := .node } else sb)
      (by rw [heffGet, hbk, Option.map_some])
    obtain ⟨h1, h2⟩ := xfc8a_demote_id_parent inp sb
    rw [h1, h2] at hx
    exact ⟨role, rect, _, hx⟩
  have hrootT2 : ∃ (role : String) (rect : Rect) (excl : Bool),
      res.scene.layoutDump.box? sg.id =
        some (Box.mk sg.id role rect sg.parent excl) := by
    obtain ⟨rect, role, hx⟩ := himg bi
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sg.id) then
        { sg with role := .node } else sg)
      (by rw [heffGet, hbi, Option.map_some])
    obtain ⟨h1, h2⟩ := xfc8a_demote_id_parent inp sg
    rw [h1, h2] at hx
    exact ⟨role, rect, _, hx⟩
  have hnotInPathB : bi ∉ Compound.path eff
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
        { sb with role := .node } else sb) := by
    intro hmem
    have hmemA : bi ∈ Compound.ancestors eff eff.length sb.parent := by
      unfold Compound.path at hmem
      split at hmem <;> exact hmem
    exact hgAnc (xfc8a_anc_of_path_mem himg hpre heffUnique hdlen' hrootT1
      (by rw [heffLen]; exact hbid) (heffIdOf bi sg hbi).1 hmemA)
  have hnotInPathG : bk ∉ Compound.path eff
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sg.id) then
        { sg with role := .node } else sg) := by
    intro hmem
    have hmemA : bk ∈ Compound.ancestors eff eff.length sg.parent := by
      unfold Compound.path at hmem
      split at hmem <;> exact hmem
    exact hbAnc (xfc8a_anc_of_path_mem himg hpre heffUnique hdlen' hrootT2
      (by rw [heffLen]; exact hbkBound) (heffIdOf bk sb hbk).1 hmemA)
  obtain ⟨gnode, hgn, hgnDecl, hgnCase⟩ :=
    xfc8a_measuredGraphNodeX execution.graph0_eq execution.graph_eq hlen heff hbi
      (by rw [heffGet, hbi, Option.map_some])
  obtain ⟨bnode, hbn, hbnDecl, hbnCase⟩ :=
    xfc8a_measuredGraphNodeX execution.graph0_eq execution.graph_eq hlen heff hbk
      (by rw [heffGet, hbk, Option.map_some])
  obtain ⟨partG, hpartGMem, entryG, hentryGMem, hentryGKey⟩ :=
    sceneExecutionX_parts_entry execution hbid
  obtain ⟨partB, hpartBMem, entryB, hentryBMem, hentryBKey⟩ :=
    sceneExecutionX_parts_entry execution hbkBound
  obtain ⟨ig, hzipG⟩ := List.mem_iff_getElem?.mp hentryGMem
  obtain ⟨ib, hzipB⟩ := List.mem_iff_getElem?.mp hentryBMem
  have higB : partG.1[ig]? = some bi := by
    have h := (List.getElem?_zip_eq_some.mp hzipG).1
    rw [hentryGKey] at h
    exact h
  have hibB : partB.1[ib]? = some bk := by
    have h := (List.getElem?_zip_eq_some.mp hzipB).1
    rw [hentryBKey] at h
    exact h
  have hcompMem : partG.1 ∈ components execution.graph := by
    rw [← hpartsMap]
    exact List.mem_map_of_mem hpartGMem
  obtain ⟨packed, hpack, -⟩ := packAcc_components_disjoint execution.packed_eq
  have hpackLen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack]
    simp
  by_cases hsame : partG = partB
  · rw [← hsame] at hibB
    obtain ⟨c, hcsel⟩ := List.mem_iff_getElem?.mp hpartGMem
    have hcbound : c < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hcsel).1
    obtain ⟨cand₀, run₀, loops₀, hrun₀, hcontain₀, hlookup₀⟩ :=
      xfc8a_part_packed_frame execution packed hpack hcsel
        (by rw [hpackLen]; exact hcbound)
    have hrectGval := hlookup₀ ig bi higB hbid
    have hrectBval := hlookup₀ ib bk hibB hbkBound
    have higne : ig ≠ ib := by
      intro heq
      rw [heq] at higB
      exact hbik (Option.some.inj (higB.symm.trans hibB))
    have hcgLen : (componentCandidate execution.graph partG.1 cand₀).nodes.length =
        partG.1.length := by
      rw [componentCandidate_nodes]
      simp [componentGraph, List.length_map]
    have hgnLookup : (componentCandidate execution.graph partG.1 cand₀).nodes[ig]? =
        some gnode := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.getElem?_map, higB, Option.map_some,
        List.getD_eq_getElem?_getD, hgn, Option.getD_some]
    have hbnLookup : (componentCandidate execution.graph partG.1 cand₀).nodes[ib]? =
        some bnode := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.getElem?_map, hibB, Option.map_some,
        List.getD_eq_getElem?_getD, hbn, Option.getD_some]
    have hcbFalse : bnode.clusterPath.contains gnode.decl = false := by
      cases hc : bnode.clusterPath.contains gnode.decl with
      | false => rfl
      | true =>
        simp only [List.contains_iff_mem] at hc
        rw [hgnDecl] at hc
        have hbc := hbnCase
        rcases hbc with ⟨_, hbPath⟩ | ⟨_, hbPath⟩
        · rw [hbPath] at hc
          rcases List.mem_append.mp hc with hmem | hmem
          · exact False.elim (hnotInPathB hmem)
          · exact False.elim (hbik (List.mem_singleton.mp hmem))
        · rw [hbPath] at hc
          exact False.elim (hnotInPathB hc)
    have hcgFalse : gnode.clusterPath.contains bnode.decl = false := by
      cases hc : gnode.clusterPath.contains bnode.decl with
      | false => rfl
      | true =>
        simp only [List.contains_iff_mem] at hc
        rw [hbnDecl] at hc
        have hgc := hgnCase
        rcases hgc with ⟨_, hgPath⟩ | ⟨_, hgPath⟩
        · rw [hgPath] at hc
          rcases List.mem_append.mp hc with hmem | hmem
          · exact False.elim (hnotInPathG hmem)
          · exact False.elim (hbik.symm (List.mem_singleton.mp hmem))
        · rw [hgPath] at hc
          exact False.elim (hnotInPathG hc)
    have hspansRun := hspans partG hpartGMem cand₀ run₀
      (candidateOrder cand₀) hrun₀
    rw [hgRect, hrectGval, hbRect, hrectBval]
    rcases hgnCase with ⟨hgBorder, -⟩ | ⟨hgBorder, -⟩
    · have hsp : Disjoint (frameRect execution.params
          (componentCandidate execution.graph partG.1 cand₀) run₀ ig)
          (frameRect execution.params
          (componentCandidate execution.graph partG.1 cand₀) run₀ ib) :=
        hspansRun ig ib gnode bnode hgnLookup hbnLookup hgBorder
          (by rw [hgnDecl, hbnDecl]; exact hbik) hcbFalse hcgFalse
      exact xfc8a_shiftRect_disjoint (xfc8a_orientRect_disjoint (xfc8a_shiftRect_disjoint
        (xfc8a_shiftRect_disjoint hsp)))
    · rcases hbnCase with ⟨hbBorder, -⟩ | ⟨hbBorder, -⟩
      · have hsp : Disjoint (frameRect execution.params
            (componentCandidate execution.graph partG.1 cand₀) run₀ ib)
            (frameRect execution.params
            (componentCandidate execution.graph partG.1 cand₀) run₀ ig) :=
          hspansRun ib ig bnode gnode hbnLookup hgnLookup hbBorder
            (by rw [hgnDecl, hbnDecl]; exact hbik.symm) hcgFalse hcbFalse
        exact (Disjoint.comm _ _).mp (xfc8a_shiftRect_disjoint (xfc8a_orientRect_disjoint
          (xfc8a_shiftRect_disjoint (xfc8a_shiftRect_disjoint hsp))))
      · have hsp : Disjoint (frameRect execution.params
            (componentCandidate execution.graph partG.1 cand₀) run₀ ig)
            (frameRect execution.params
            (componentCandidate execution.graph partG.1 cand₀) run₀ ib) :=
          hpos execution.graph0_eq execution.graph_eq hcompMem hrun₀
            hgnLookup hbnLookup hgBorder hbBorder higne
        exact xfc8a_shiftRect_disjoint (xfc8a_orientRect_disjoint (xfc8a_shiftRect_disjoint
          (xfc8a_shiftRect_disjoint hsp)))
  · obtain ⟨cG, hcselG⟩ := List.mem_iff_getElem?.mp hpartGMem
    obtain ⟨cB, hcselB⟩ := List.mem_iff_getElem?.mp hpartBMem
    have hcGbound : cG < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hcselG).1
    have hcBbound : cB < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hcselB).1
    obtain ⟨candB, runB, loopsB, hrunB, hcontainB, hlookupB⟩ :=
      xfc8a_part_packed_frame execution packed hpack hcselB
        (by rw [hpackLen]; exact hcBbound)
    obtain ⟨candG, runG, loopsG, hrunG, hcontainG, hlookupG⟩ :=
      xfc8a_part_packed_frame execution packed hpack hcselG
        (by rw [hpackLen]; exact hcGbound)
    have hcpboxG : packed.boxes[cG]? = some packed.boxes[cG] :=
      List.getElem?_eq_getElem (by rw [hpackLen]; exact hcGbound)
    have hcpboxB : packed.boxes[cB]? = some packed.boxes[cB] :=
      List.getElem?_eq_getElem (by rw [hpackLen]; exact hcBbound)
    have hcne : cG ≠ cB := by
      intro heq
      apply hsame
      have h1 : (execution.componentsAcc.parts.zip packed.boxes)[cG]? =
          some (partG, packed.boxes[cG]) := List.getElem?_zip_eq_some.mpr ⟨hcselG, hcpboxG⟩
      have h2 : (execution.componentsAcc.parts.zip packed.boxes)[cB]? =
          some (partB, packed.boxes[cB]) := List.getElem?_zip_eq_some.mpr ⟨hcselB, hcpboxB⟩
      have hsel1 := zip_getElem?_left h1
      have hsel2 := zip_getElem?_left h2
      rw [heq] at hsel1
      exact Option.some.inj (hsel1.symm.trans hsel2)
    have hdisjRects : Disjoint packed.boxes[cG] packed.boxes[cB] :=
      Pack.pack_boxes_disjoint hpack cG cB
        (by rw [hpackLen]; exact hcGbound) (by rw [hpackLen]; exact hcBbound) hcne
    have hvalG := hlookupG ig bi higB hbid
    have hvalB := hlookupB ib bk hibB hbkBound
    have hconG := hcontainG ig bi higB hbid
    have hconB := hcontainB ib bk hibB hbkBound
    rw [hgRect, hvalG, hbRect, hvalB]
    intro hmeet
    exact hdisjRects (meetsInterior_contained_mono
      (meetsInterior_of_orientRect (meetsInterior_of_shiftRect hmeet)) hconG hconB)

/-- Flat C8a for the exact pipeline. -/
theorem flatC8aB_layoutX (exactIds : List String)
    (hcluster : XB_ForeignClusterRankSpans exactIds)
    (hlayer : XB_ForeignBorderLayerOrder exactIds)
    (hchain : X_ForeignBorderChainXAligned exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignSide : XN_SideMarkerSpanAligned exactIds) :
    FlatC8aB (layoutX exactIds) := by
  intro inp o res hwf hfp h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hgroups : XB_ForeignBorderSpansSeparated exactIds :=
    xfc8a_groups_of hcluster hlayer hchain
  have hothers : XN_ForeignNonGroupSpansClear exactIds :=
    xfc8a_others_of hbracket hplain halignSide
  have hlen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    unfold boxLines at hl
    have h2 := (mapM_getElem? _ _ _ hl).1
    have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
    omega
  have hpartsMap : execution.componentsAcc.parts.map (·.1) = components execution.graph :=
    (actual_components_parts_geometryX (by rfl) execution.components_eq).1
  apply xfc8a_layout_c8a_executedX execution hwf hfp _ XS_C8a_PositionsDisjoint_of_run
  intro part hpart candidate run orderOptions hrun
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hpartsMap]
    exact List.mem_map_of_mem hpart
  exact xfc8a_spansClear_of_run execution.graph0_eq execution.graph_eq hlen hwf hfp
    hgroups hothers hcomp hrun
end PipelineImpl
end Layered
end Elegant
