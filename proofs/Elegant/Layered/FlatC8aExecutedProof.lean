import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.FrameClearanceSeam
import ElegantGeometry.Validator

set_option autoImplicit false

/-! # Execution-level flat foreign-frame clearance (`Validator.C8a`)

`layout_c8a_executed` is the execution-level form of `layout_c8a`: it takes
the `SceneExecution` directly instead of the successful flat layout equation.
The layout equation is consumed exactly once in `layout_c8a`, to extract the
execution via `layout_sceneExecution`; no overflow or budget check of `layout`
is used afterwards. Every subsequent step (dump box identity, id uniqueness,
ancestor translation, graph node lookup, part membership, packed geometry)
already goes through `SceneExecution` fields, so the proof below is the same
argument with the extraction step replaced by the given execution.

`flatC8a_executed` composes this with the same three seam arguments that
`flatC8a_of_span_seams` takes, for the fallback-owner lane which only has an
execution in hand.
-/

namespace Elegant.Layered

namespace PipelineImpl

local instance : Inhabited ModelBox := ⟨{ id := "" }⟩

/-! ### Executed-level copies of the flat-C8a private helpers -/

/-- Two members of a list with nodup keys that carry equal keys are equal. -/
private theorem getElem_unique_of_nodup_map_e {α : Type} {f : α → String} {l : List α}
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

/-- Demoting a fixed-size box to node role keeps its id and parent. -/
private theorem demote_id_parent_e (inp : Input) (b : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b).id = b.id ∧
      (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b).parent = b.parent := by
  split <;> simp

/-- The graph node behind one input box: declaration index and the model ancestor
path (`Compound.path` of the demoted box), with the box's own index appended when
the demoted role is a group (so the node is the executed frame node). -/
private theorem measuredGraphNode_e {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlen : lines.length = inp.boxes.length)
    {eff : List ModelBox}
    (heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)
    {k : Nat} {s : ModelBox} {sg : ModelBox}
    (hk : inp.boxes[k]? = some s)
    (hsg : eff[k]? = some sg) :
    ∃ node : Node,
      graph.nodes[k]? = some node ∧
      node.decl = k ∧
      ((node.border = -2 ∧ node.clusterPath = Compound.path eff sg ++ [k]) ∨
        (node.border = 0 ∧ node.clusterPath = Compound.path eff sg)) := by
  obtain ⟨nodes, edges, titles, hprepared, hnodesLen, hmeta⟩ :=
    measuredGraph_prepared_source hgraph
  have hkLen : k < lines.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hk).1
  have hkNodes : k < nodes.length := by rw [hnodesLen]; exact hkLen
  obtain ⟨hn0decl, hn0border⟩ := hmeta k nodes[k] (List.getElem?_eq_getElem hkNodes)
  rw [hprepared]
  rw [heff] at hsg
  by_cases hrole : sg.role = .group
  · -- group: title record
    have hrec := Compound.prepare_group_title_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles ⟨nodes, edges, P.slot⟩ hkNodes hsg hrole
    rw [hrec]
    rw [← heff]
    refine ⟨{ nodes[k]'hkNodes with
      clusterPath := Compound.path eff sg ++ [k]
      border := -2
      w := (titles.getD k (0, 0)).1
      h := if nodes[k].loopExtent == 0 then (titles.getD k (0, 0)).2 + P.clusterPad
        else max ((titles.getD k (0, 0)).2 + P.clusterPad) nodes[k].h },
      rfl, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · simp [hn0decl]
  · -- non-group: plain node record
    have hrec := Compound.prepare_plain_node_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles ⟨nodes, edges, P.slot⟩ hkNodes hsg hrole
    rw [hrec]
    rw [← heff]
    refine ⟨{ nodes[k]'hkNodes with clusterPath := Compound.path eff sg }, rfl, ?_,
      Or.inr ⟨hn0border, rfl⟩⟩
    · simp [hn0decl]

 /-- A strict model ancestor index is an id of the dump ancestor walk. -/
 private theorem compound_mem_dump_go_e {boxes : List ModelBox} {d : LayoutDump}
     (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
       ∃ (rect : Rect) (role : String),
         d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive))
     (_hpre : ∀ bx : Box, bx ∈ d.boxes →
       ∃ b : ModelBox, b ∈ boxes ∧ b.id = bx.id ∧ b.parent = bx.parent)
     (_hid : ∀ (a b : ModelBox), a ∈ boxes → b ∈ boxes → a.id = b.id → a = b) :
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
     · subst s
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
     · subst s
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

 private theorem anc_of_path_mem_e {boxes : List ModelBox} {d : LayoutDump}
     (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
       ∃ (rect : Rect) (role : String),
         d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive))
     (hpre : ∀ bx : Box, bx ∈ d.boxes →
       ∃ b : ModelBox, b ∈ boxes ∧ b.id = bx.id ∧ b.parent = bx.parent)
     (hid : ∀ (a b : ModelBox), a ∈ boxes → b ∈ boxes → a.id = b.id → a = b)
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
         · have hgo2 := compound_mem_dump_go_e himg hpre hid fuel p idx hmem hidx hself
           rw [hs] at hgo2
           exact List.mem_cons.mpr (Or.inr hgo2)

 private theorem packed_inner_contained_e {bounds : Bounds} {frame : Rect} {w h : Int}
     (hw : w = bounds.right - bounds.minX) (hh : h = bounds.bottom - bounds.minY)
     (hin : bounds.minX ≤ frame.x ∧ frame.x + frame.w ≤ bounds.right ∧
       bounds.minY ≤ frame.y ∧ frame.y + frame.h ≤ bounds.bottom) :
     (⟨0, 0, w, h⟩ : Rect).Contained (shiftRect (0 - bounds.minX) (0 - bounds.minY) frame) := by
   simp only [Rect.Contained, shiftRect]
   subst hw
   subst hh
   omega

 private theorem shiftRect_disjoint_e {a b : Rect} {dx dy : Int}
     (h : Disjoint a b) : Disjoint (shiftRect dx dy a) (shiftRect dx dy b) := by
   simp only [Disjoint, Rect.meetsInterior, shiftRect] at h ⊢
   omega

 private theorem orientRect_disjoint_e {a b : Rect} {d : Direction} {h : Int}
     (hm : Disjoint a b) : Disjoint (orientRect d h a) (orientRect d h b) := by
   intro hc
   exact hm (meetsInterior_of_orientRect hc)

 private theorem shiftRect_zero_self_e (r : Rect) :
     shiftRect r.x r.y ⟨0, 0, r.w, r.h⟩ = r := by
   simp [shiftRect]

 private theorem placeComponent_width_e (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
     (placeComponent P cg run 0 labels loops).width =
       (placeBounds P cg run labels loops).right -
         (placeBounds P cg run labels loops).minX := rfl

 private theorem placeComponent_height_e (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
     (placeComponent P cg run 0 labels loops).height =
       (placeBounds P cg run labels loops).bottom -
         (placeBounds P cg run labels loops).minY := rfl

 private theorem placeComponent_rects_get_e (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
     {i : Nat} (hi : i < cg.nodes.length) :
     (placeComponent P cg run 0 labels loops).rects[i]? =
       some (shiftRect (0 - (placeBounds P cg run labels loops).minX)
         (0 - (placeBounds P cg run labels loops).minY)
         (frameRect P cg run i)) := by
   unfold placeComponent placeBounds
   simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

 /-! ### Foreign frame clearance for an executed flat layout -/
 set_option maxHeartbeats 2000000 in
 /-- Execution-level form of `layout_c8a`: the dump of the scene carried by a
 successful execution keeps every group frame disjoint from boxes that are
 neither its ancestors nor its descendants. The per-run premise is stated for
 the given execution only. -/
 theorem layout_c8a_executed {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     (hforeign : ∀ (part : List Nat × Part),
         part ∈ execution.componentsAcc.parts →
         ForeignFramePartClear execution.params execution.measured
           execution.graph part.1) :
     Validator.C8a res.scene.layoutDump := by
   have _ := hframed
   have hboxesEq : res.scene.layoutDump.boxes = (inp.boxes.zipIdx.map fun q =>
       Box.mk q.1.id q.1.role.id
         (shiftRect execution.params.canvasMargin execution.params.canvasMargin
           (orientRect o.direction execution.packedAcc.canvasH
             (execution.packedAcc.rects.getD q.2 default)))
         q.1.parent q.1.exclusive) := by
     simp [Scene.layoutDump, execution.boxes_eq_map]
   have hlen : execution.lines.length = inp.boxes.length :=
     boxLines_length execution.lines_eq
   have hdlen : res.scene.layoutDump.boxes.length = inp.boxes.length := by
     rw [hboxesEq, List.length_map, List.length_zipIdx]
   have hpartsMap : execution.componentsAcc.parts.map (·.1) = components execution.graph := by
     have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
         Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
         false, [], []⟩ : Acc).parts = [] := rfl
     exact (actual_components_parts_geometry (P := execution.params) (inp := inp)
       (o := o) (g := execution.graph) (labels := execution.measured) hempty
       execution.components_eq).1
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
     intro k; rw [heff, List.getElem?_map]
   have heffNodup : (eff.map (·.id)).Nodup := by
     have hcongr : eff.map (·.id) = inp.boxes.map (·.id) := by
       rw [heff, List.map_map]
       congr 1
       funext b
       exact (demote_id_parent_e inp b).1
     rw [hcongr]
     exact hidsNodup
   have heffUnique : ∀ (a b : ModelBox), a ∈ eff → b ∈ eff → a.id = b.id → a = b :=
     fun a b ha hb hid => getElem_unique_of_nodup_map_e heffNodup ha hb hid
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
       obtain ⟨h1, h2⟩ := demote_id_parent_e inp orig
       have h3 : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
           { orig with role := .node } else orig).exclusive = orig.exclusive := by
         split <;> rfl
       rw [h1, h2, h3]
       exact ⟨_, _, execution.source_box_lookup hwf hin⟩
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
       · rw [(demote_id_parent_e inp q.1).1, ← hqeq]
       · rw [(demote_id_parent_e inp q.1).2, ← hqeq]
   have hdlen' : res.scene.layoutDump.boxes.length = eff.length := by
     rw [heffLen]; exact hdlen
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
     exact demote_id_parent_e inp s
   have hrootT1 : ∃ (role : String) (rect : Rect) (excl : Bool),
       res.scene.layoutDump.box? sb.id =
         some (Box.mk sb.id role rect sb.parent excl) := by
     obtain ⟨rect, role, hx⟩ := himg bk
       (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
         { sb with role := .node } else sb)
       (by rw [heffGet, hbk, Option.map_some])
     obtain ⟨h1, h2⟩ := demote_id_parent_e inp sb
     rw [h1, h2] at hx
     exact ⟨role, rect, _, hx⟩
   have hrootT2 : ∃ (role : String) (rect : Rect) (excl : Bool),
       res.scene.layoutDump.box? sg.id =
         some (Box.mk sg.id role rect sg.parent excl) := by
     obtain ⟨rect, role, hx⟩ := himg bi
       (if inp.fixedSizes.any (fun fixed => fixed.1 == sg.id) then
         { sg with role := .node } else sg)
       (by rw [heffGet, hbi, Option.map_some])
     obtain ⟨h1, h2⟩ := demote_id_parent_e inp sg
     rw [h1, h2] at hx
     exact ⟨role, rect, _, hx⟩
   have hnotInPathB : bi ∉ Compound.path eff
       (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
         { sb with role := .node } else sb) := by
     intro hmem
     have hmemA : bi ∈ Compound.ancestors eff eff.length sb.parent := by
       unfold Compound.path at hmem
       split at hmem <;> exact hmem
     exact hgAnc (anc_of_path_mem_e (s := sg.id) himg hpre heffUnique hdlen' hrootT1
       (by rw [heffLen]; exact hbid) (heffIdOf bi sg hbi).1 hmemA)
   have hnotInPathG : bk ∉ Compound.path eff
       (if inp.fixedSizes.any (fun fixed => fixed.1 == sg.id) then
         { sg with role := .node } else sg) := by
     intro hmem
     have hmemA : bk ∈ Compound.ancestors eff eff.length sg.parent := by
       unfold Compound.path at hmem
       split at hmem <;> exact hmem
     exact hbAnc (anc_of_path_mem_e (s := sb.id) himg hpre heffUnique hdlen' hrootT2
       (by rw [heffLen]; exact hbkBound) (heffIdOf bk sb hbk).1 hmemA)
   -- graph nodes of both boxes
   obtain ⟨gnode, hgn, hgnDecl, hgnCase⟩ :=
     measuredGraphNode_e execution.graph_eq hlen heff hbi
       (by rw [heffGet, hbi, Option.map_some])
   obtain ⟨bnode, hbn, hbnDecl, hbnCase⟩ :=
     measuredGraphNode_e execution.graph_eq hlen heff hbk
       (by rw [heffGet, hbk, Option.map_some])
   -- both boxes appear in some executed part
   obtain ⟨partG, hpartGMem, entryG, hentryGMem, hentryGKey⟩ :=
     sceneExecution_parts_entry execution hbid
   obtain ⟨partB, hpartBMem, entryB, hentryBMem, hentryBKey⟩ :=
     sceneExecution_parts_entry execution hbkBound
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
   -- pack state
   obtain ⟨packed, hpack, -⟩ := packAcc_components_disjoint execution.packed_eq
   have hpackLen : packed.boxes.length = execution.componentsAcc.parts.length := by
     rw [Pack.pack_count hpack]
     simp
   -- packed box dimensions follow the part items
   have pdim : ∀ (part : List Nat × Part) (c : Nat)
       (hc : execution.componentsAcc.parts[c]? = some part)
       (hcb : c < packed.boxes.length),
       packed.boxes[c].w = part.2.width ∧ packed.boxes[c].h = part.2.height := by
     intro part c hc hcb
     have hdim := Pack.pack_dimensions hpack
     unfold Pack.dimensions at hdim
     have h1 : (packed.boxes.map fun r => (r.w, r.h))[c]? =
         some (packed.boxes[c].w, packed.boxes[c].h) := by
       simp only [List.getElem?_map, List.getElem?_eq_getElem hcb, Option.map_some]
     have h2 : ((execution.componentsAcc.parts.map fun q =>
           (⟨q.2.width, q.2.height, q.2.area⟩ : Pack.Item)).map
         fun i => (i.width, i.height))[c]? =
         some (part.2.width, part.2.height) := by
       simp only [List.getElem?_map, hc, Option.map_some]
     rw [hdim, h2] at h1
     have hp := Option.some.inj h1
     exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩

   by_cases hsame : partG = partB
   · -- same component: reduce to the executed run frame rectangles
     rw [← hsame] at hibB
     obtain ⟨_, hall⟩ := actual_components_parts_geometry (P := execution.params)
       (inp := inp) (o := o) (g := execution.graph) (labels := execution.measured)
       (by rfl) execution.components_eq
     obtain ⟨cand₀, _, run₀, loops₀, _, hallc⟩ := hall partG hpartGMem
     obtain ⟨_, _, _, hrun₀, _, hpartdef⟩ := hallc
     let cg₀ : Graph := componentCandidate execution.graph partG.1 cand₀
     have hcgLen : cg₀.nodes.length = partG.1.length := by
       rw [componentCandidate_nodes]
       simp [componentGraph, List.length_map]
     -- packed box selection at index c
     obtain ⟨c, hcsel⟩ := List.mem_iff_getElem?.mp hpartGMem
     have hcbound : c < execution.componentsAcc.parts.length :=
       (List.getElem?_eq_some_iff.mp hcsel).1
     have hcpbox : packed.boxes[c]? = some packed.boxes[c] :=
       List.getElem?_eq_getElem (by rw [hpackLen]; exact hcbound)
     let pbox := packed.boxes[c]
     have hsel : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
         some (partG, pbox) := List.getElem?_zip_eq_some.mpr ⟨hcsel, hcpbox⟩
     let bnd := placeBounds execution.params cg₀ run₀ execution.measured loops₀
     have hrectAt : ∀ (key idx : Nat) (_ : key < inp.boxes.length)
         (hIdx : partG.1[idx]? = some key),
         execution.packedAcc.rects.getD key default =
           shiftRect pbox.x pbox.y (shiftRect (0 - bnd.minX) (0 - bnd.minY)
             (frameRect execution.params cg₀ run₀ idx)) := by
       intro key idx hkeyBound hIdx
       have hilen : idx < cg₀.nodes.length := by
         rw [hcgLen]
         exact (List.getElem?_eq_some_iff.mp hIdx).1
       have hrect : partG.2.rects[idx]? = some (shiftRect (0 - bnd.minX)
           (0 - bnd.minY) (frameRect execution.params cg₀ run₀ idx)) := by
         rw [hpartdef]
         exact placeComponent_rects_get_e execution.params cg₀ run₀ execution.measured
           loops₀ hilen
       have hentry : (partG.1.zip partG.2.rects)[idx]? =
           some (key, shiftRect (0 - bnd.minX) (0 - bnd.minY)
             (frameRect execution.params cg₀ run₀ idx)) :=
         List.getElem?_zip_eq_some.mpr ⟨hIdx, hrect⟩
       have hsize : key < execution.componentsAcc.rects.size := by
         rw [execution.components_rects_size]; exact hkeyBound
       exact actual_components_packed_rect_value (by rfl)
         execution.components_eq execution.packed_eq packed hpack hsel hentry
         hsize default
     have hrectGval := hrectAt bi ig hbid higB
     have hrectBval := hrectAt bk ib hbkBound hibB
     have higne : ig ≠ ib := by
       intro heq
       rw [heq] at higB
       exact hbik (Option.some.inj (higB.symm.trans hibB))
     -- candidate-level node lookups
     have hgnLookup : cg₀.nodes[ig]? = some gnode := by
       rw [componentCandidate_nodes]
       simp only [componentGraph, List.getElem?_map, higB, Option.map_some,
         List.getD_eq_getElem?_getD, hgn, Option.getD_some]
     have hbnLookup : cg₀.nodes[ib]? = some bnode := by
       rw [componentCandidate_nodes]
       simp only [componentGraph, List.getElem?_map, hibB, Option.map_some,
         List.getD_eq_getElem?_getD, hbn, Option.getD_some]
     -- contains-false facts from the ancestor translation
     have hcbFalse : bnode.clusterPath.contains gnode.decl = false := by
       cases hc : bnode.clusterPath.contains gnode.decl with
       | false => rfl
       | true =>
         simp only [List.contains_iff_mem] at hc
         rw [hgnDecl] at hc
         have hbc := hbnCase
         rcases hbc with ⟨-, hbPath⟩ | ⟨-, hbPath⟩
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
         rcases hgc with ⟨-, hgPath⟩ | ⟨-, hgPath⟩
         · rw [hgPath] at hc
           rcases List.mem_append.mp hc with hmem | hmem
           · exact False.elim (hnotInPathG hmem)
           · exact False.elim (hbik.symm (List.mem_singleton.mp hmem))
         · rw [hgPath] at hc
           exact False.elim (hnotInPathG hc)
     -- premise application
     obtain ⟨_, hspans⟩ := hforeign partG hpartGMem cand₀ run₀
       (candidateOrder cand₀) hrun₀
     rw [hgRect, hrectGval, hbRect, hrectBval]
     rcases hgnCase with ⟨hgBorder, -⟩ | ⟨hgBorder, -⟩
     · have hsp : Disjoint (frameRect execution.params cg₀ run₀ ig)
           (frameRect execution.params cg₀ run₀ ib) :=
         hspans ig ib gnode bnode hgnLookup hbnLookup hgBorder
           (by rw [hgnDecl, hbnDecl]; exact hbik) hcbFalse hcgFalse
       exact shiftRect_disjoint_e (orientRect_disjoint_e (shiftRect_disjoint_e
         (shiftRect_disjoint_e hsp)))
     · rcases hbnCase with ⟨hbBorder, -⟩ | ⟨hbBorder, -⟩
       · have hsp : Disjoint (frameRect execution.params cg₀ run₀ ib)
             (frameRect execution.params cg₀ run₀ ig) :=
           hspans ib ig bnode gnode hbnLookup hgnLookup hbBorder
             (by rw [hgnDecl, hbnDecl]; exact hbik.symm) hcgFalse hcbFalse
         exact (Disjoint.comm _ _).mp (shiftRect_disjoint_e (orientRect_disjoint_e
           (shiftRect_disjoint_e (shiftRect_disjoint_e hsp))))
       · exact shiftRect_disjoint_e (orientRect_disjoint_e (shiftRect_disjoint_e
           (shiftRect_disjoint_e (componentRun_positions_disjoint execution.graph_eq
             hcompMem hrun₀ hgnLookup hbnLookup hgBorder hbBorder higne))))
   · -- different components: disjoint packed boxes
     obtain ⟨_, hall⟩ := actual_components_parts_geometry (P := execution.params)
       (inp := inp) (o := o) (g := execution.graph) (labels := execution.measured)
       (by rfl) execution.components_eq
     obtain ⟨candG, _, runG, loopsG, areaG, hallG⟩ := hall partG hpartGMem
     obtain ⟨_, _, _, _, _, hpartdefG⟩ := hallG
     obtain ⟨candB, _, runB, loopsB, areaB, hallB⟩ := hall partB hpartBMem
     obtain ⟨_, _, _, _, _, hpartdefB⟩ := hallB
     obtain ⟨cG, hcselG⟩ := List.mem_iff_getElem?.mp hpartGMem
     obtain ⟨cB, hcselB⟩ := List.mem_iff_getElem?.mp hpartBMem
     have hcGbound : cG < execution.componentsAcc.parts.length :=
       (List.getElem?_eq_some_iff.mp hcselG).1
     have hcBbound : cB < execution.componentsAcc.parts.length :=
       (List.getElem?_eq_some_iff.mp hcselB).1
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
     have pdim : ∀ (part : List Nat × Part) (c : Nat)
         (hc : execution.componentsAcc.parts[c]? = some part)
         (hcb : c < packed.boxes.length),
         packed.boxes[c].w = part.2.width ∧ packed.boxes[c].h = part.2.height := by
       intro part c hc hcb
       have hdim := Pack.pack_dimensions hpack
       unfold Pack.dimensions at hdim
       have h1 : (packed.boxes.map fun r => (r.w, r.h))[c]? =
           some (packed.boxes[c].w, packed.boxes[c].h) := by
         simp only [List.getElem?_map, List.getElem?_eq_getElem hcb, Option.map_some]
       have h2 : ((execution.componentsAcc.parts.map fun q =>
             (⟨q.2.width, q.2.height, q.2.area⟩ : Pack.Item)).map
           fun i => (i.width, i.height))[c]? =
           some (part.2.width, part.2.height) := by
         simp only [List.getElem?_map, hc, Option.map_some]
       rw [hdim, h2] at h1
       have hp := Option.some.inj h1
       exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
     -- per-part packed rect value, bounds identities, and containment
     have hkeyval : ∀ (part : List Nat × Part) (cand : Nat) (run : Run)
         (loops : List (Nat × LoopPlacement))
         (hpd : ∃ w : Int, part.2 = { placeComponent execution.params
             (componentCandidate execution.graph part.1 cand) run 0 execution.measured
             loops with area := w })
         (pbox : Rect) (c : Nat) (hc : execution.componentsAcc.parts[c]? = some part)
         (hpbox : packed.boxes[c]? = some pbox)
         (key : Nat) (hkeyBound : key < inp.boxes.length) (hkeyMem : key ∈ part.1),
         ∃ (i : Nat) (bounds : Bounds),
           execution.packedAcc.rects.getD key default =
             shiftRect pbox.x pbox.y (shiftRect (0 - bounds.minX) (0 - bounds.minY)
               (frameRect execution.params
                 (componentCandidate execution.graph part.1 cand) run i)) ∧
           pbox.w = bounds.right - bounds.minX ∧
           pbox.h = bounds.bottom - bounds.minY ∧
           pbox.Contained (shiftRect pbox.x pbox.y (shiftRect (0 - bounds.minX)
             (0 - bounds.minY)
             (frameRect execution.params
               (componentCandidate execution.graph part.1 cand) run i))) := by
       intro part cand run loops hpd pbox c hc hpbox key hkeyBound hkeyMem
       obtain ⟨w, hpd⟩ := hpd
       let cgP : Graph := componentCandidate execution.graph part.1 cand
       have hcgLen : cgP.nodes.length = part.1.length := by
         rw [componentCandidate_nodes]
         simp [componentGraph, List.length_map]
       obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hkeyMem
       have hilen : i < cgP.nodes.length := by
         rw [hcgLen]; exact (List.getElem?_eq_some_iff.mp hi).1
       have hrect : part.2.rects[i]? = some (shiftRect
           (0 - (placeBounds execution.params cgP run execution.measured loops).minX)
           (0 - (placeBounds execution.params cgP run execution.measured loops).minY)
           (frameRect execution.params cgP run i)) := by
         rw [hpd]
         exact placeComponent_rects_get_e execution.params cgP run execution.measured
           loops hilen
       have hentry : (part.1.zip part.2.rects)[i]? = some
           (key, shiftRect
             (0 - (placeBounds execution.params cgP run execution.measured loops).minX)
             (0 - (placeBounds execution.params cgP run execution.measured loops).minY)
             (frameRect execution.params cgP run i)) :=
         List.getElem?_zip_eq_some.mpr ⟨hi, hrect⟩
       have hsize : key < execution.componentsAcc.rects.size := by
         rw [execution.components_rects_size]; exact hkeyBound
       have hsel : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
           some (part, pbox) := List.getElem?_zip_eq_some.mpr ⟨hc, hpbox⟩
       have hval := actual_components_packed_rect_value (by rfl)
         execution.components_eq execution.packed_eq packed hpack hsel hentry
         hsize default
       have hcb : c < packed.boxes.length := (List.getElem?_eq_some_iff.mp hpbox).1
       have hcbox : packed.boxes[c] = pbox := (List.getElem?_eq_some_iff.mp hpbox).2
       have hwid : pbox.w =
           (placeBounds execution.params cgP run execution.measured loops).right -
             (placeBounds execution.params cgP run execution.measured loops).minX := by
         rw [← hcbox, (pdim part c hc hcb).1, hpd]
         exact placeComponent_width_e execution.params cgP run execution.measured loops
       have hhei : pbox.h =
           (placeBounds execution.params cgP run execution.measured loops).bottom -
             (placeBounds execution.params cgP run execution.measured loops).minY := by
         rw [← hcbox, (pdim part c hc hcb).2, hpd]
         exact placeComponent_height_e execution.params cgP run execution.measured loops
       have hmemRect : frameRect execution.params cgP run i ∈
           (List.range cgP.nodes.length).map (frameRect execution.params cgP run) :=
         List.mem_map_of_mem (f := frameRect execution.params cgP run)
           (List.mem_range.mpr hilen)
       have hmemAll : frameRect execution.params cgP run i ∈
           (List.range cgP.nodes.length).map (frameRect execution.params cgP run) ++
             ((List.range cgP.nodes.length).map (frameRect execution.params cgP run)).zipIdx.map
                 (fun q => ⟨q.1.x + q.1.w, q.1.y,
                   Loops.extent cgP.slot
                     (loopSizes cgP.edges execution.measured q.2 cgP.slot), q.1.h⟩) ++
               labelBounds execution.params cgP run execution.measured ++
                 (componentTitles execution.params cgP run).map (·.2) :=
         List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmemRect))
       have hinBounds : (placeBounds execution.params cgP run execution.measured loops).minX ≤
           (frameRect execution.params cgP run i).x ∧
           (frameRect execution.params cgP run i).x + (frameRect execution.params cgP run i).w ≤
             (placeBounds execution.params cgP run execution.measured loops).right ∧
           (placeBounds execution.params cgP run execution.measured loops).minY ≤
           (frameRect execution.params cgP run i).y ∧
           (frameRect execution.params cgP run i).y + (frameRect execution.params cgP run i).h ≤
             (placeBounds execution.params cgP run execution.measured loops).bottom :=
         Elegant.Layered.boundsOf_contains_rect hmemAll
       have hmid0 : pbox.Contained (shiftRect pbox.x pbox.y (shiftRect
           (0 - (placeBounds execution.params cgP run execution.measured loops).minX)
           (0 - (placeBounds execution.params cgP run execution.measured loops).minY)
           (frameRect execution.params cgP run i))) := by
         have h0 := contained_shiftRect_imp
           (dx := pbox.x) (dy := pbox.y)
           (a := ⟨0, 0, pbox.w, pbox.h⟩)
           (packed_inner_contained_e hwid hhei hinBounds)
         rw [shiftRect_zero_self_e pbox] at h0
         exact h0
       exact ⟨i, placeBounds execution.params cgP run execution.measured loops,
         hval, hwid, hhei, hmid0⟩
     have hkeyInG : bi ∈ partG.1 := by
       rw [← hentryGKey]
       exact (List.of_mem_zip hentryGMem).1
     have hkeyInB : bk ∈ partB.1 := by
       rw [← hentryBKey]
       exact (List.of_mem_zip hentryBMem).1
     have hx := hkeyval partG candG runG loopsG ⟨areaG, hpartdefG⟩ packed.boxes[cG] cG hcselG hcpboxG bi hbid hkeyInG
     obtain ⟨iG, bndsG, hvalG, hwidG, hheiG, hmidG⟩ := hx
     obtain ⟨iB, bndsB, hvalB, hwidB, hheiB, hmidB⟩ :=
       hkeyval partB candB runB loopsB ⟨areaB, hpartdefB⟩ packed.boxes[cB] cB hcselB hcpboxB bk
       hbkBound hkeyInB
     rw [hgRect, hvalG, hbRect, hvalB]
     intro hmeet
     refine hdisjRects ?_
     exact meetsInterior_contained_mono
       (meetsInterior_of_orientRect (meetsInterior_of_shiftRect hmeet))
       hmidG hmidB

 /-- The flat foreign-frame clause for an executed layout: `FlatC8a` with the
 successful flat layout equation replaced by the execution it produced. Takes
 the same three seam arguments as `flatC8a_of_span_seams`. -/
 theorem flatC8a_executed {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
     (hgroups : ForeignBorderSpansSeparated) (hothers : ForeignNonGroupSpansClear)
     (hbracket : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       BracketInsidePremises inp o res) :
     Validator.C8a res.scene.layoutDump := by
   apply layout_c8a_executed execution hwf hfp
   intro part hpart
   have hmap : execution.componentsAcc.parts.map (·.1) = components execution.graph := by
     have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
         Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
         false, [], []⟩ : Acc).parts = [] := rfl
     exact (actual_components_parts_geometry (P := execution.params) (inp := inp)
       (o := o) (g := execution.graph) (labels := execution.measured) hempty
       execution.components_eq).1
   have hcomp : part.1 ∈ components execution.graph :=
     part_component_mem hmap hpart
   intro candidate run orderOptions hrun
   have hlinesLen : execution.lines.length = inp.boxes.length :=
     boxLines_length execution.lines_eq
   exact ⟨frameClearanceSeam_holds (hbracket inp o res hwf hfp)
       execution part.1 candidate run orderOptions hcomp hrun,
     foreignSpansClear_of_run hgroups hothers execution.graph_eq hlinesLen
       hwf hfp hcomp hrun⟩

 end PipelineImpl

 end Elegant.Layered
