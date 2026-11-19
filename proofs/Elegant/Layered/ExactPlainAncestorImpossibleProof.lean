import Elegant.Layered.ExactCaptionAncestorsProof
import Elegant.Layered.ExactCaptionMembersProof
import Elegant.Layered.CaptionRunClearClosed
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Compound
import Elegant.Layered.PipelineFacts
import Elegant.Layered.FamilyC5B
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.Pipeline

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact plain-ancestor impossibility (standalone leaf)

Proves `XCA_PlainAncestorImpossibleX exactIds` in its W form (local
`WellFormed (inputModel inp o)` and `framedParents inp = true` over the
executed `measuredGraph` / `exactGraph` pair): no border-`-2` title node has a
border-`0` plain node in its cluster path. The argument replays declaration
index reasoning across `exactGraph`: a border-`0` candidate node carries its
source index as declaration with the input box path as cluster path, and on
the title path it is an ancestor index, hence a group in the demoted list,
while its demoted box is not a group.

Full proof with no residual defs and no open goals. The statement proved here
is exactly the `ExactSeams.capImpossible` leaf. The theorem name differs from
`XCA_plainAncestorImpossibleX_holds` in `ExactCaptionAncestorFactsProof` only
to keep public names unique; that module holds an independent proof of the
same leaf.

Truth comes first: the five `#eval` lines below execute the exact pipeline on
nested groups, a self-loop, a zero-size fixed child, an empty group, and one
ill-formed input, counting border-`-2` / border-`0` ancestor pairs over every
component and candidates 0-2. The first four report zero pairs with framed
parents and matching line counts; the ill-formed input reports its prep
outcome.
-/

/-! ## Truth: executed exact inputs -/

private def epaiGBox (id parent : String) : ModelBox :=
  { id := id, role := .group, parent := parent, exclusive := false }

private def epaiNBox (id parent : String) : ModelBox :=
  { id := id, parent := parent, exclusive := false }

private def epaiRt (id fromId toId : String) : ModelRoute :=
  { id := id, fromId := fromId, toId := toId }

/-- Nested groups `G > H > m` with an edge to the outside. -/
private def epaiNested : Input :=
  { kind := "flowchart"
    boxes := [epaiGBox "G" "", epaiGBox "H" "G", epaiNBox "m" "H", epaiNBox "o" ""]
    routes := [epaiRt "e1" "m" "o"]
    texts := ["G", "H", "m", "o"]
    edges := [.plain]
    labels := [] }

/-- Self-loop inside a group plus an outgoing edge. -/
private def epaiSelf : Input :=
  { kind := "flowchart"
    boxes := [epaiGBox "G" "", epaiNBox "m" "G", epaiNBox "o" ""]
    routes := [epaiRt "e1" "m" "m", epaiRt "e2" "m" "o"]
    texts := ["G", "m", "o"]
    edges := [.plain, .plain]
    labels := [] }

/-- Zero-size fixed member: `a` keeps a `0 x 0` frame. -/
private def epaiZero : Input :=
  { kind := "flowchart"
    boxes := [epaiGBox "G1" "", epaiNBox "a" "G1", epaiGBox "G2" "", epaiNBox "b" "G2"]
    routes := [epaiRt "e1" "a" "b"]
    texts := ["G1", "a", "G2", "b"]
    edges := [.plain]
    fixedSizes := [("a", ⟨0, 0⟩)]
    labels := [] }

/-- Empty group: no member boxes at all. -/
private def epaiEmpty : Input :=
  { kind := "flowchart"
    boxes := [epaiGBox "G" "", epaiNBox "a" "", epaiNBox "b" ""]
    routes := [epaiRt "e1" "a" "b"]
    texts := ["G", "a", "b"]
    edges := [.plain]
    labels := [] }

/-- Ill-formed: route target does not exist. -/
private def epaiIll : Input :=
  { kind := "flowchart"
    boxes := [epaiGBox "G" "", epaiNBox "a" "G"]
    routes := [epaiRt "e1" "a" "zzz"]
    texts := ["G", "a"]
    edges := [.plain]
    labels := [] }

private def epaiPrep (inp : Input) (o : Options) (exactIds : List String) :
    Except LayoutError (Params × List (List Measure.Line) × List MeasuredLabel × Graph) := do
  let P ← checkedParams o.profile inp.kind
  let m ← metricOf o.profile
  let target := Measure.wrapTarget m.profile P.wrapWidth
    (if o.profile == .cell then o.maxWidth else 0)
  let lines ← boxLines m target inp
  let labels ← measureLabels P m target inp o.direction
  let g0 ← measuredGraph P inp o lines
  let g ← exactGraph P exactIds inp o labels g0
  pure (P, lines, labels, g)

private def epaiCountPairs (g : Graph) (comp : List Nat) (candidate : Nat) : Nat :=
  let cg := componentCandidate g comp candidate
  let idx := List.range cg.nodes.length
  idx.foldl (fun acc tIdx =>
    idx.foldl (fun acc2 fIdx =>
      match cg.nodes[tIdx]?, cg.nodes[fIdx]? with
      | some tN, some fN =>
        if tN.border == -2 && fN.border == 0 && tN.decl != fN.decl &&
            tN.clusterPath.contains fN.decl then acc2 + 1 else acc2
      | _, _ => acc2) acc) 0

private def epaiReport (name : String) (inp : Input) (o : Options)
    (exactIds : List String) : String :=
  match epaiPrep inp o exactIds with
  | .error e => s!"{name}: prep rejects {repr e}\n"
  | .ok (_P, lines, _labels, g) =>
    let comps := components g
    let fp := framedParents inp
    let linesOk := lines.length == inp.boxes.length
    let counts := [0, 1, 2].map (fun cand =>
      (comps.map (fun comp => epaiCountPairs g comp cand)).foldl (· + ·) 0)
    s!"{name}: nodes={g.nodes.length} comps={repr comps} framed={fp} linesOk={linesOk} pairs={repr counts}\n"

#eval epaiReport "nested" epaiNested {} []
#eval epaiReport "selfLoop" epaiSelf {} []
#eval epaiReport "zeroSize" epaiZero {} ["a"]
#eval epaiReport "emptyGroup" epaiEmpty {} []
#eval epaiReport "illFormed" epaiIll {} []

/-! ## Proof: declaration-index transport across `exactGraph` -/

/-- `epai_` copy of `components_mem_bound_copy`
(`CaptionRunClearClosed.lean:45`): component members index valid nodes. -/
private theorem epai_mem_bound {g : Graph} {comp : List Nat}
    (hmem : comp ∈ components g) {v : Nat} (hv : v ∈ comp) :
    v < g.nodes.length := by
  unfold components at hmem
  dsimp only at hmem
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hmem
  rw [← hr] at hv
  exact List.mem_range.mp (List.mem_filter.mp hv).1

/-- `epai_` copy of `otherClear_demote_facts` (`CaptionRunClearClosed.lean:56`):
the demoted box keeps id, parent, and exclusivity. -/
private theorem epai_demote_facts {inp : Input} (box : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).id = box.id ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).parent = box.parent ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).exclusive = box.exclusive := by
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- `epai_` copy of `otherClear_getElem_unique`
(`CaptionRunClearClosed.lean:67`): injectivity of the id map on nodup lists. -/
private theorem epai_getElem_unique {α : Type} {f : α → String} {l : List α}
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

/-- `epai_` copy of `xca_key_rev` (`ExactCaptionAncestorsProof.lean:247`):
drop from an exact node back to its measured source. -/
private theorem epai_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g')
    {v : Nat} {nd' : Node} (hv : g'.nodes[v]? = some nd') :
    ∃ nd, g.nodes[v]? = some nd ∧ nd'.border = nd.border ∧
      nd'.clusterPath = nd.clusterPath ∧ nd'.decl = nd.decl := by
  have hlen : g'.nodes.length = g.nodes.length := exactGraph_length h
  have hvlt : v < g.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have hmem : g.nodes[v]? = some g.nodes[v] := List.getElem?_eq_getElem hvlt
  obtain ⟨nd'', hnd'', hb, hc, hd⟩ := exactGraph_node_key h hmem
  have heq : nd'' = nd' := Option.some.inj (hnd''.symm.trans hv)
  subst heq
  exact ⟨g.nodes[v], hmem, hb, hc, hd⟩

/-- `epai_` copy of `xca_demoteId` (`ExactCaptionAncestorsProof.lean:155`):
demotion keeps ids. -/
private theorem epai_demoteId {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) b).id = b.id := by
  intro b _
  dsimp only
  split <;> rfl

/-- `epai_` copy of `xca_demoteParent` (`ExactCaptionAncestorsProof.lean:162`):
demotion keeps parents. -/
private theorem epai_demoteParent {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) b).parent = b.parent := by
  intro b _
  dsimp only
  split <;> rfl

/-- `epai_` copy of `xca_demoteLookup`
(`ExactCaptionAncestorsProof.lean:170`): invert a fixed-boxes lookup. -/
private theorem epai_demoteLookup {inp : Input} {i : Nat} {b : ModelBox}
    (h : (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)[i]? = some b) :
    ∃ orig : ModelBox, inp.boxes[i]? = some orig ∧ b.id = orig.id ∧ b.parent = orig.parent ∧
      (b.role = .group → ¬(inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) = true)) ∧
      b = (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then { orig with role := .node } else orig) := by
  rw [List.getElem?_map] at h
  cases hop : inp.boxes[i]? with
  | none => rw [hop] at h; simp at h
  | some orig =>
    rw [hop, Option.map_some, Option.some.injEq] at h
    by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == orig.id)
    · have hd : b = ({ orig with role := .node } : ModelBox) := h.symm.trans (ite_eq_left hfixed)
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_, by rw [hd, ite_eq_left hfixed]⟩
      intro hrole
      rw [hd] at hrole
      simp at hrole
    · have hd : b = orig := h.symm.trans (ite_eq_right (by simp [hfixed]))
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_, by rw [hd, ite_eq_right hfixed]⟩
      intro _
      exact hfixed

/-- `epai_` copy of `XCM_plain_path`
(`ExactCaptionMembersProof.lean:167`): measured-graph plain node source,
taking the graph equation and line count directly. -/
private theorem epai_plain_path {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph0 : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hlines : lines.length = inp.boxes.length)
    {index : Nat} {node : Node} (hnode : graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  obtain ⟨nodes, _edges, _titles, hprepared, hnodesLen, hmetadata⟩ :=
    measuredGraph_prepared_source h0
  have hpreparedNode := hnode
  rw [hprepared] at hpreparedNode
  have hi : index < nodes.length := by
    by_cases hi : index < nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
        hpreparedNode
      omega
  have hibox : index < inp.boxes.length := by
    have hlen : nodes.length = inp.boxes.length := by rw [hnodesLen, hlines]
    omega
  let box := inp.boxes[index]'hibox
  have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
  exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩

/-- `epai_` copy of `otherClear_path_group_role`
(`CaptionRunClearClosed.lean:87`): every member of an `ancestors` walk is a
group in the demoted box list. -/
private theorem epai_path_group_role {inp : Input}
    (hfp : framedParents inp = true)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (eff : List ModelBox)
    (heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)
    (fuel : Nat) (c : ModelBox) (hc : c ∈ inp.boxes) :
    ∀ i ∈ Compound.ancestors eff fuel c.parent,
      ∃ b, eff[i]? = some b ∧ b.role = .group := by
  induction fuel generalizing c with
  | zero =>
    intro i hi
    have hempty : Compound.ancestors eff 0 c.parent = [] := rfl
    rw [hempty] at hi
    simp at hi
  | succ fuel ih =>
    intro i hi
    by_cases hcp : c.parent = ""
    · have hnil : Compound.ancestors eff (fuel + 1) c.parent = [] := by
        simp [hcp, Compound.ancestors]
      rw [hnil] at hi
      simp at hi
    · have h3 := Compound.ancestors.eq_3 eff c.parent fuel hcp
      rw [h3] at hi
      cases hf : eff.findIdx? (fun box => box.id == c.parent) with
      | none =>
        simp only [hf] at hi
        simp at hi
      | some j =>
        simp only [hf] at hi
        cases hb : eff[j]? with
        | none =>
          simp only [hb] at hi
          simp at hi
        | some e =>
          simp only [hb] at hi
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have heid : e.id = c.parent := by
            rw [← hbjEq]
            exact beq_iff_eq.mp hjid
          have heffj : eff[j]? = (inp.boxes[j]?).map fun b =>
              if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
                { b with role := .node } else b := by
            rw [heff, List.getElem?_map]
          rw [heffj] at hb
          cases hjo : inp.boxes[j]? with
          | none => rw [hjo] at hb; exact absurd hb (by simp)
          | some orig =>
            rw [hjo] at hb
            have heq : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                { orig with role := .node } else orig) = e := Option.some.inj hb
            have horig : orig ∈ inp.boxes := List.mem_of_getElem? hjo
            have hdemParent : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                { orig with role := .node } else orig).parent = orig.parent :=
              (epai_demote_facts orig).2.1
            have heid' : orig.id = c.parent := by
              have hroleD : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                  { orig with role := .node } else orig).id = orig.id :=
                (epai_demote_facts orig).1
              have heid'' := heid
              rw [← heq] at heid''
              exact hroleD.symm.trans heid''
            have hbE : eff[j]? = some e := by
              rw [heffj, hjo]
              exact congrArg some heq
            simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hi | rfl
            · rw [← heq, hdemParent] at hi
              exact ih orig horig i hi
            · refine ⟨e, hbE, ?_⟩
              rw [← heq]
              have hall : (c.parent == "" ||
                  inp.boxes.any fun parent =>
                    parent.id == c.parent && parent.role == .group &&
                      !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id)) = true :=
                List.all_eq_true.mp hfp c hc
              have hOr : (c.parent == "") = true ∨
                  (inp.boxes.any fun parent =>
                    parent.id == c.parent && parent.role == .group &&
                      !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id)) = true := by
                by_cases hblank : (c.parent == "") = true
                · exact Or.inl hblank
                · right
                  have hfalse : (c.parent == "") = false := by
                    cases h2 : (c.parent == "") with
                    | true => exact absurd h2 hblank
                    | false => rfl
                  simp only [hfalse, Bool.false_or] at hall
                  exact hall
              rcases hOr with hblank | hany
              · exact absurd (beq_iff_eq.mp hblank) hcp
              · obtain ⟨pb, hpbmem, hpb⟩ := List.any_eq_true.mp hany
                simp only [Bool.and_eq_true] at hpb
                obtain ⟨⟨hpbIdB, hpbRoleB⟩, hpbNotFixB⟩ := hpb
                have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
                have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
                have hnotfix : inp.fixedSizes.any
                    (fun fixed => fixed.1 == pb.id) = false := by
                  simpa using hpbNotFixB
                have horigEq : orig = pb :=
                  epai_getElem_unique hids horig hpbmem (by
                    rw [heid']; exact hpbId.symm)
                have hdem : (if inp.fixedSizes.any (fun fixed => fixed.1 == pb.id) then
                    { pb with role := .node } else pb) = pb := by
                  simp [hnotfix]
                rw [horigEq, hdem]
                exact hpbRole

/-- Plain-ancestor impossibility over exact runs: replay of
`captionAncestorOtherClear_executed` (`CaptionRunClearClosed.lean:205`) with
the measured-graph origins transported across `exactGraph`. A border-`0`
candidate node carries its source-graph index as declaration and the input
box path as cluster path (`epai_plain_path`); on the title path it is an
ancestor index, hence a group in the demoted list
(`epai_path_group_role`), while its demoted box is not a group
(`prepare_group_title_record` contrapositive). Proves the
`ExactSeams.capImpossible` leaf `XCA_PlainAncestorImpossibleX`. -/
theorem exactPlainAncestorImpossible_holds (exactIds : List String) :
    XCA_PlainAncestorImpossibleX exactIds := by
  intro P inp o lines measured graph0 graph h0 hgraph hlines hwf hframed
  intro comp hcomp candidate tNode fNode tIdx fIdx hnode hborder hfn hb0 hne hancrel
  obtain ⟨origT, _, hsrcT⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨ndT0, hndT0, hbT0, hpT0, hdT0⟩ := epai_key_rev hgraph hsrcT
  have hbT0' : ndT0.border = -2 := hbT0.symm.trans hborder
  obtain ⟨hdeclT0, boxTE, hboxTE, _, hpathT0⟩ :=
    measuredGraph_group_origin h0 hndT0 hbT0'
  have hdeclT : tNode.decl = origT := hdT0.trans hdeclT0
  obtain ⟨origTU, horigTU, _, _, _, hdemTU⟩ := epai_demoteLookup hboxTE
  have horigT : inp.boxes[origT]? = some origTU := hdeclT0 ▸ horigTU
  have hpmU : Compound.path (inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box) boxTE =
      Compound.path inp.boxes origTU := by
    have hpm := Compound.path_map inp.boxes
      (fun box => if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box)
      epai_demoteId epai_demoteParent (List.mem_of_getElem? horigT)
    rw [← hdemTU] at hpm
    exact hpm
  have hpathTEq : tNode.clusterPath = Compound.path inp.boxes origTU ++ [tNode.decl] := by
    rw [hpT0, hpathT0, hpmU, ← hdT0]
  rw [componentCandidate_nodes] at hfn
  have hmap : (componentGraph graph comp).nodes =
      comp.map (fun v => graph.nodes.getD v default) := rfl
  rw [hmap, List.getElem?_map] at hfn
  obtain ⟨origP, hcompP, hgetP⟩ := Option.map_eq_some_iff.mp hfn
  have hmemP : origP ∈ comp := List.mem_of_getElem? hcompP
  have hltP : origP < graph.nodes.length :=
    epai_mem_bound hcomp hmemP
  obtain ⟨n, hn⟩ : ∃ n, graph.nodes[origP]? = some n :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨hltP, rfl⟩⟩
  have hget : graph.nodes.getD origP default = n := by
    simp [List.getD_eq_getElem?_getD, hn]
  rw [hget] at hgetP
  rw [hgetP] at hn
  obtain ⟨ndP0, hndP0, hbP0, _hpP0, hdP0⟩ := epai_key_rev hgraph hn
  have hbP0' : ndP0.border = 0 := hbP0.symm.trans hb0
  obtain ⟨boxP, hboxP, hdeclP, _hpathP⟩ := epai_plain_path h0 hlines hndP0 hbP0'
  have hdeclP' : fNode.decl = origP := hdP0.trans hdeclP
  rw [hpathTEq, hdeclP', hdeclT] at hancrel
  have hnePO : origP ≠ origT :=
    fun hcon => hne (hdeclT.trans (hcon.symm.trans hdeclP'.symm))
  have hmemAppend : origP ∈ Compound.path inp.boxes origTU ++ [origT] := by
    have hdec : decide (origP ∈ Compound.path inp.boxes origTU ++ [origT]) = true := by
      rw [← List.contains_eq_mem]
      exact hancrel
    exact of_decide_eq_true hdec
  rcases List.mem_append.mp hmemAppend with hleft | hright
  · let eff : List ModelBox := inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b
    let chT : ModelBox := (if inp.fixedSizes.any (fun fixed => fixed.1 == origTU.id) then
      { origTU with role := .node } else origTU)
    let chP : ModelBox := (if inp.fixedSizes.any (fun fixed => fixed.1 == boxP.id) then
      { boxP with role := .node } else boxP)
    obtain ⟨_, heffP, _⟩ := fixedSizes_path_index inp hboxP
    obtain ⟨_, _, hpathMapT⟩ := fixedSizes_path_index inp horigT
    have hpathT_eq : Compound.path eff chT = Compound.path inp.boxes origTU :=
      hpathMapT
    have heffP' : eff[origP]? = some chP := heffP
    have hdemT : chT.parent = origTU.parent := (epai_demote_facts origTU).2.1
    have hmemFuel : origP ∈ Compound.ancestors eff eff.length origTU.parent := by
      have hmemChT : origP ∈ Compound.path eff chT := by
        rw [hpathT_eq]
        exact hleft
      rw [← hdemT]
      exact hmemChT
    have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
    obtain ⟨b, hb, hrole⟩ := epai_path_group_role hframed hids eff rfl
      eff.length origTU (List.mem_of_getElem? horigT) origP hmemFuel
    have hbeq : b = chP := Option.some.inj (hb.symm.trans heffP')
    subst hbeq
    obtain ⟨nodes, edges, titles, hprepared, hnodesLen, _⟩ :=
      measuredGraph_prepared_source h0
    have hltLen : origP < nodes.length := by
      rw [hnodesLen, hlines]
      exact (List.getElem?_eq_some_iff.mp hboxP).1
    have hpreparedNode : (Compound.prepare eff P.clusterPad titles
        { nodes := nodes, edges := edges,
          slot := P.slot }).nodes[origP]? = some ndP0 := by
      have h := hndP0
      rw [hprepared] at h
      exact h
    have hroleNe : chP.role ≠ .group := by
      intro hgroup
      have hrec := Compound.prepare_group_title_record eff P.clusterPad
        titles { nodes := nodes, edges := edges, slot := P.slot }
        hltLen heffP' hgroup
      have heq := Option.some.inj (hpreparedNode.symm.trans hrec)
      have hb2 : ndP0.border = -2 := congrArg Node.border heq
      rw [hbP0'] at hb2
      omega
    exact absurd hrole hroleNe
  · have hsingleton : origP = origT := List.mem_singleton.mp hright
    exact absurd hsingleton hnePO

end PipelineImpl
end Layered
end Elegant
