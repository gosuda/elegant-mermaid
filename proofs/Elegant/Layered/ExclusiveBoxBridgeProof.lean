import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.SizingCoverageBridge

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Residual: for a well-formed framed input, the declaration of an
exclusive-sourced box never occurs in the cluster path of any node of an
executed component candidate graph.  Id statement only: an exclusive box is
never a group (`WellFormed` forbids exclusive groups), while every
cluster-path member indexes a group box (`framedParents` makes every parent
a group, and group title nodes carry their own group index).  True for
executed layouts, strictly simpler than the bridge goal, about the measured
graph phase, and pinned by the `SceneExecution` graph equation. -/
def ExclusiveKeyOutsideCgPaths (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  WellFormed (inputModel inp o) → framedParents inp = true →
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (v key : Nat) (source : ModelBox),
    comp ∈ components execution.graph →
    comp[v]? = some key →
    inp.boxes[key]? = some source →
    source.exclusive = true →
    ∀ (u : Nat) (nd : Node),
      (componentCandidate execution.graph comp candidate).nodes[u]? = some nd →
      key ∉ nd.clusterPath

/-- A candidate graph has exactly the component's nodes. -/
private theorem candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- A pair selected from the packed zip projects to the shelf selected from
the packed boxes at the same index. -/
private theorem zip_getElem?_right {α β : Type} {xs : List α} {ys : List β}
    {c : Nat} {x : α} {y : β} (h : (xs.zip ys)[c]? = some (x, y)) :
    ys[c]? = some y :=
  (List.getElem?_zip_eq_some.mp h).2

/-- The exclusive box bridge of the route label seam, with pinned transports.
An exclusive dump box outside the label's owner scope is either the executed
transport of the `boxRect` of a real node of the label's own run (same packed
part), or the content of another packed part.  The scope hypothesis is
subsumed by the id residuals and therefore unused; the label-side hypotheses
tie the witness to the label but the box split needs only the part pins. -/
theorem exclusiveBoxInLabelRun {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hdecl : ExclusiveRunNodeDecl inp o res)
    (hkey : ExclusiveKeyOutsideCgPaths inp o res) :
    ExclusiveBoxInLabelRun inp o res := by
  intro execution l index source measured comp candidate run cg _edge _decl e
    packed c labelPart shelfc loops area rl
    _hlmem _hin _hid _hmeasured hcomp hcg hrun _he _hdeclmap _hmlabel hpacked hselected
    hpart1 hpartdef hrlmem hlrect b hdump hex _hscope
  subst hcg
  have hboxes : b ∈ res.scene.boxes := hdump
  rw [execution.boxes_eq_map] at hboxes
  obtain ⟨⟨bsource, key⟩, hq, rfl⟩ := List.mem_map.mp hboxes
  have hsource : inp.boxes[key]? = some bsource :=
    List.mem_zipIdx_iff_getElem?.mp hq
  have hkeylen : key < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hexcl : bsource.exclusive = true := hex
  have hgraphlen : key < execution.graph.nodes.length :=
    sceneExecution_graph_len execution hkeylen
  have hgnode : execution.graph.nodes[key]? =
      some (execution.graph.nodes[key]'hgraphlen) := List.getElem?_eq_getElem hgraphlen
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  by_cases hmem : key ∈ labelPart.1
  · -- Same part: the box is the transported `boxRect` of the run node at `key`.
    obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
    have hcompv : comp[v]? = some key := by
      rw [← hpart1]; exact hv
    have hvlen : v < (componentCandidate execution.graph comp candidate).nodes.length := by
      rw [candidate_nodes_length]
      exact (List.getElem?_eq_some_iff.mp hcompv).1
    have hproper : v < run.proper.nodes.length :=
      componentRun_original_nodes_covered hrun v hvlen
    have hcgnode := candidate_node_of_part_key (index := candidate) hcompv hgnode
    have hreal := componentRun_source_isReal hrun hcgnode
    have hnodeDecl : RouteImpl.nodeDecl run.proper v = key :=
      hdecl execution comp candidate run hcomp hrun v key bsource hcompv hsource
    have hs0 : RouteImpl.nodeDecl run.proper v ∉
        (((componentCandidate execution.graph comp candidate).nodes[e.tail]?).map
          (·.clusterPath)).getD [] := by
      rw [hnodeDecl]
      cases htail : (componentCandidate execution.graph comp candidate).nodes[e.tail]? with
      | none => simp
      | some nd =>
        simp only [Option.getD_some, Option.map_some]
        exact hkey hwf hframed execution comp candidate v key bsource
          hcomp hcompv hsource hexcl e.tail nd htail
    have hs1 : RouteImpl.nodeDecl run.proper v ∉
        (((componentCandidate execution.graph comp candidate).nodes[e.head]?).map
          (·.clusterPath)).getD [] := by
      rw [hnodeDecl]
      cases hhead : (componentCandidate execution.graph comp candidate).nodes[e.head]? with
      | none => simp
      | some nd =>
        simp only [Option.getD_some, Option.map_some]
        exact hkey hwf hframed execution comp candidate v key bsource
          hcomp hcompv hsource hexcl e.head nd hhead

    have hentry := chosen_part_frame_entry (P := execution.params)
      (graph := execution.graph) (component := labelPart.1) (candidate := candidate)
      (run := run) (labels := execution.measured) (loops := loops)
      (part := labelPart.2) (area := area)
      (hpart := by rw [hpart1]; exact hpartdef) hv
    have hval := actual_components_packed_rect_value hempty execution.components_eq
      execution.packed_eq packed hpacked hselected hentry hkeysize default

    have hborder : ((componentCandidate execution.graph comp candidate).nodes.getD v
        default).border ≠ -2 := by
      have hnode : bsource.role = BoxRole.node := by
        have hnotgroup : bsource.role ≠ BoxRole.group := by
          intro hg
          obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
          have hexf := hgroups bsource (List.mem_of_getElem? hsource) hg
          rw [hexf] at hexcl
          exact Bool.noConfusion hexcl
        cases hr : bsource.role with
        | node => rfl
        | group => exact absurd hr hnotgroup
      have hkey' : labelPart.1[v]? = some key := hv
      rw [hpart1] at hkey'
      exact execution.effective_candidate_node_not_top (component := comp)
        (candidate := candidate) (v := v) (key := key) (source := bsource)
        hkey' hsource (Or.inl hnode)
    have hframe := plain_frame_eq_boxRect execution.params
      (componentCandidate execution.graph comp candidate) run v hproper hborder
    refine Or.inl ⟨v, hproper, hreal, hs0, hs1, ?_⟩
    have hbrect : (Box.mk bsource.id bsource.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)))
        bsource.parent bsource.exclusive).rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default)) := rfl
    rw [hbrect, hval, hpart1, hframe, shiftRect_shiftRect]
  · -- Other part: label and box come from two distinct packed shelves.
    obtain ⟨boxPart, hboxPartmem, entry, hentrymem, hentrykey⟩ :=
      sceneExecution_parts_entry execution hkeylen
    have hkeymem : key ∈ boxPart.1 := by
      have hmemzip : (key, entry.2) ∈ boxPart.1.zip boxPart.2.rects := by
        have heq : entry = (key, entry.2) := congrArg (·, entry.2) hentrykey
        rw [heq] at hentrymem
        exact hentrymem
      exact (List.of_mem_zip hmemzip).1
    have hne : boxPart.1 ≠ labelPart.1 := by
      intro hcontra
      rw [hcontra] at hkeymem
      exact hmem hkeymem
    obtain ⟨d', hd'⟩ := List.mem_iff_getElem?.mp hboxPartmem
    have hd'len : d' < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hd').1
    have hboxlen : packed.boxes.length = execution.componentsAcc.parts.length := by
      rw [Pack.pack_count hpacked, List.length_map]
    have hshelf : packed.boxes[d']? = some packed.boxes[d'] :=
      List.getElem?_eq_getElem (by rw [hboxlen]; exact hd'len)
    have hselected' : (execution.componentsAcc.parts.zip packed.boxes)[d']? =
        some (boxPart, packed.boxes[d']) :=
      List.getElem?_zip_eq_some.mpr ⟨hd', hshelf⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hentrymem

    have hentry2 : (boxPart.1.zip boxPart.2.rects)[i]? = some (key, entry.2) := by
      have heq : entry = (key, entry.2) := congrArg (·, entry.2) hentrykey
      rw [heq] at hi
      exact hi
    have hval' := actual_components_packed_rect_value hempty execution.components_eq
      execution.packed_eq packed hpacked hselected' hentry2 hkeysize default
    have hcpart : execution.componentsAcc.parts[c]? = some labelPart :=
      zip_getElem?_left hselected
    have hcshelf : packed.boxes[c]? = some shelfc :=
      zip_getElem?_right hselected
    have hdpart : execution.componentsAcc.parts[d']? = some boxPart := hd'
    have hdshelf : packed.boxes[d']? = some packed.boxes[d'] := hshelf
    have hc'ne : c ≠ d' := by
      intro heq
      have hqc : execution.componentsAcc.parts[c]? = some boxPart := by
        rw [heq]; exact hdpart
      have hpe : labelPart = boxPart := Option.some.inj (hcpart.symm.trans hqc)
      rw [hpe] at hne
      exact hne rfl
    refine Or.inr ⟨packed, c, d', labelPart, boxPart, shelfc, packed.boxes[d'],
      rl, entry.2, hpacked, hcpart, hcshelf, hdpart, hdshelf, hc'ne, hrlmem,
      (List.of_mem_zip hentrymem).2, hlrect, ?_⟩
    have hbrect : (Box.mk bsource.id bsource.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)))
        bsource.parent bsource.exclusive).rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default)) := rfl
    rw [hbrect, hval']

end PipelineImpl
end Layered
end Elegant
