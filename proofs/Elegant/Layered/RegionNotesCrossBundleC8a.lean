import Elegant.Layered.RegionNotesSameBundleC8a
import Elegant.Layered.RegionNotesMixedC8a
import Elegant.Layered.RegionPositionsDisjoint
import Elegant.Layered.LabelsC8bFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private abbrev regionNotesBase (idSets : List (String × List String)) :
    List String → Input → Options → Except LayoutError FamilyResult :=
  fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o

private theorem contractOne_node_source {inp : Input} {l : BundleLayout} {b : ModelBox}
    (hb : b ∈ (contractOne inp l).boxes) :
    ∃ a ∈ inp.boxes, a.id = b.id ∧ (b.id = l.top.id → b.role = .node) ∧
      (a.role = .node → b.role = .node) := by
  simp only [contractOne, List.mem_map, List.mem_filter] at hb
  obtain ⟨q, ⟨hq, _⟩, rfl⟩ := hb
  have ha := List.fst_mem_of_mem_zipIdx hq
  by_cases htop : q.1.id == l.top.id
  · rw [ite_eq_left htop]
    exact ⟨q.1, ha, rfl, fun _ => rfl, fun _ => rfl⟩
  · rw [ite_eq_right htop]
    exact ⟨q.1, ha, rfl, fun h => (htop (beq_iff_eq.mpr h)).elim, id⟩

private theorem contractFold_top_node (ls : List BundleLayout) (inp : Input) {b : ModelBox}
    (hb : b ∈ (ls.foldl contractOne inp).boxes) :
    (∀ l ∈ ls, l.top.id = b.id → b.role = .node) ∧
      ∃ a ∈ inp.boxes, a.id = b.id ∧ (a.role = .node → b.role = .node) := by
  induction ls generalizing inp with
  | nil => exact ⟨by simp, b, hb, rfl, id⟩
  | cons l rest ih =>
    rw [List.foldl_cons] at hb
    obtain ⟨htops, a, ha, hid, hnode⟩ := ih (contractOne inp l) hb
    obtain ⟨src, hsrc, hsrcId, htop, hpreserve⟩ := contractOne_node_source ha
    refine ⟨?_, src, hsrc, hsrcId.trans hid, fun h => hnode (hpreserve h)⟩
    intro k hk heq
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hnode (htop (hid.trans heq.symm))
    · exact htops k hk heq

private theorem envelope_lookup_id {s : Scene} {l : BundleLayout} {env : Box}
    (h : s.boxes.find? (·.id == l.top.id) = some env) : env.id = l.top.id :=
  beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == l.top.id) h)

theorem regionNotes_envelope_exists {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) :
    ∃ env, e.contracted.scene.boxes.find? (·.id == l.top.id) = some env := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨_, hrun, _⟩ := (mapM_getElem? _ _ _ e.placed_eq).2 i l hi
  cases h : e.contracted.scene.boxes.find? (·.id == l.top.id) with
  | none =>
    unfold placedFragments at hrun
    rw [h] at hrun
    cases hrun
  | some env => exact ⟨env, rfl⟩

/-- A bundle envelope is a plain node of the contracted run even when the emitted top is a group. -/
theorem regionNotes_envelope_role_node {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) {env : Box}
    (h : e.contracted.scene.boxes.find? (·.id == l.top.id) = some env) :
    env.role = "node" := by
  obtain ⟨b, hb, hid, _, _, hrole⟩ := (layoutRIds_boxes_mirror e.contracted_eq).2 env
    (List.mem_of_find?_eq_some h)
  rw [e.contractedInput_eq] at hb
  have htop := (envelope_lookup_id h).symm.trans hid
  have hnode := (contractFold_top_node e.layouts inp hb).1 l hl htop
  simp [hrole, hnode, BoxRole.id]

private theorem envelopeSibling_disjoint {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) {env cb : Box}
    (henv : e.contracted.scene.boxes.find? (·.id == l.top.id) = some env)
    (hcb : cb ∈ e.contracted.scene.boxes) (hne : env.id ≠ cb.id)
    (hrole : cb.role ≠ "group") (hpar : env.parent = cb.parent) :
    Disjoint env.rect cb.rect := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution e.contracted_eq
  exact execution.nodeSiblings_disjoint (List.mem_of_find?_eq_some henv) hcb hne
    (by rw [regionNotes_envelope_role_node (idSets := idSets) e hl henv]; decide) hrole hpar

/-- Distinct bundle envelopes that are siblings in the contracted scene are disjoint. -/
theorem regionNotes_siblingEnvelopes_disjoint {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    {a b : BundleLayout} (ha : a ∈ e.layouts) (hb : b ∈ e.layouts) (hne : a.top.id ≠ b.top.id)
    {ea eb : Box}
    (hea : e.contracted.scene.boxes.find? (·.id == a.top.id) = some ea)
    (heb : e.contracted.scene.boxes.find? (·.id == b.top.id) = some eb)
    (hparent : ea.parent = eb.parent) :
    Disjoint (envRect e.contracted.scene a) (envRect e.contracted.scene b) := by
  simp only [envRect, hea, heb]
  exact envelopeSibling_disjoint (idSets := idSets) e ha hea (List.mem_of_find?_eq_some heb)
    (by simpa only [envelope_lookup_id hea, envelope_lookup_id heb] using hne)
    (by rw [regionNotes_envelope_role_node (idSets := idSets) e hb heb]; decide) hparent

/-- Actual fragment boxes from different sibling bundles stay clear, including restored group frames. -/
theorem regionNotes_crossSibling_fragments_disjoint {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    {a b : BundleLayout} (ha : a ∈ e.layouts) (hb : b ∈ e.layouts) (hne : a.top.id ≠ b.top.id)
    {ea eb : Box}
    (hea : e.contracted.scene.boxes.find? (·.id == a.top.id) = some ea)
    (heb : e.contracted.scene.boxes.find? (·.id == b.top.id) = some eb)
    (hparent : ea.parent = eb.parent) {p q : Placed}
    (hp : p ∈ placedOf' e.margin e.contracted.scene a)
    (hq : q ∈ placedOf' e.margin e.contracted.scene b)
    {sb tb : Box} (hsb : sb ∈ p.scene.boxes) (htb : tb ∈ q.scene.boxes) :
    Disjoint (shiftRect p.dx p.dy sb.rect) (shiftRect q.dx q.dy tb.rect) := by
  have hfit := regionNotes_envelope_contains (idSets := idSets) e
  exact disjoint_of_contained_disjoint (hfit a ha p hp sb hsb) (hfit b hb q hq tb htb)
    (regionNotes_siblingEnvelopes_disjoint (idSets := idSets) e ha hb hne hea heb hparent)

/-- The envelope residual now ranges only over actual envelopes with different parents. -/
def NotesC8aEnvDisjExceptSiblings
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ a ∈ e.layouts, ∀ b ∈ e.layouts, a.top.id ≠ b.top.id →
    ∀ ea eb : Box,
      e.contracted.scene.boxes.find? (·.id == a.top.id) = some ea →
      e.contracted.scene.boxes.find? (·.id == b.top.id) = some eb →
      ea.parent ≠ eb.parent → Disjoint (envRect e.contracted.scene a) (envRect e.contracted.scene b)

theorem notesC8aEnvDisj_of_exceptSiblings {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    (hremain : NotesC8aEnvDisjExceptSiblings e) : NotesC8aEnvDisj e := by
  intro a ha b hb hne
  obtain ⟨ea, hea⟩ := regionNotes_envelope_exists (idSets := idSets) e ha
  obtain ⟨eb, heb⟩ := regionNotes_envelope_exists (idSets := idSets) e hb
  by_cases hparent : ea.parent = eb.parent
  · exact regionNotes_siblingEnvelopes_disjoint (idSets := idSets) e ha hb hne hea heb hparent
  · exact hremain a ha b hb hne ea eb hea heb hparent

/-- An unclaimed id cannot be a bundle top: the top is placed in a fragment. -/
theorem regionNotes_unclaimed_ne_bundleTop {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) {id : String}
    (hfree : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect id ≠ some r) : l.top.id ≠ id := by
  intro hsame
  have hfrag : fragmentIdOf inp l id = true := by
    simp only [fragmentIdOf, hsame, beq_self_eq_true, Bool.true_or]
  obtain ⟨p, hp, hboxes⟩ := List.any_eq_true.mp
    (notesC8aFragFound_layoutR (idSets := idSets) e l hl id hfrag)
  obtain ⟨b, hb, hid⟩ := List.any_eq_true.mp hboxes
  have hmem : p ∈ e.fragments := by
    rw [e.fragments_eq]
    exact placedOf_mem_flatten e.placed_eq hl hp
  cases hfind : p.scene.boxes.find? (·.id == id) with
  | none => exact (List.find?_eq_none.mp hfind b hb) hid
  | some sb =>
    exact hfree p hmem (shiftRect p.dx p.dy sb.rect) (by simp only [Placed.rect, hfind, Option.map_some])

/-- An unclaimed contracted box retains its source role. Only a bundle top can change roles. -/
theorem regionNotes_unclaimed_source_role {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (regionNotesBase idSets) exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) {cb : Box}
    (hcb : cb ∈ e.contracted.scene.boxes)
    (hfree : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) :
    ∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = cb.role := by
  have hcontract := notesC8aContractRoleT_holds e (inputFacts_of_wellFormed hwf).nodup (by
    intro b hb
    obtain ⟨source, hsource, hid, _, _, hrole⟩ :=
      (layoutRIds_boxes_mirror e.contracted_eq).2 b hb
    rw [e.contractedInput_eq] at hsource
    exact ⟨source, hsource, hid.symm, hrole⟩)
  obtain ⟨ib, hlookup, hrole⟩ := hcontract cb hcb
  rcases hrole with hsame | ⟨l, hl, htop, _, _⟩
  · exact ⟨ib, List.mem_of_find?_eq_some hlookup,
      beq_iff_eq.mp (List.find?_some (p := fun b : ModelBox => b.id == cb.id) hlookup), hsame⟩
  · exact (regionNotes_unclaimed_ne_bundleTop (idSets := idSets) e hl hfree htop).elim

end Elegant.Layered.PipelineImpl
