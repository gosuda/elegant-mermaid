import Elegant.Layered.NotesFoundation
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.RecursiveFit

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Box metadata from the actual layout of a selected, rooted note subinput. -/
abbrev NoteSelectionBoxSources (inp : Input) (keep : ModelBox → Bool) (root : String)
    (scene : Scene) : Prop :=
  ∀ b ∈ scene.boxes, ∃ x ∈ (subInput inp keep root).boxes,
    b.id = x.id ∧ b.parent = x.parent ∧ b.exclusive = x.exclusive

private theorem noteSubInput_box_source {inp : Input} {keep : ModelBox → Bool} {root : String}
    {x : ModelBox} (hx : x ∈ (subInput inp keep root).boxes) :
    ∃ a ∈ inp.boxes, keep a = true ∧ x.id = a.id ∧ x.exclusive = a.exclusive ∧
      x.parent = (if a.id == root then "" else a.parent) := by
  change x ∈ (selectInput inp keep).boxes.map (fun b =>
    if b.id == root then { b with parent := "" } else b) at hx
  obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
  change b ∈ (inp.boxes.zipIdx.filter (fun q => keep q.1)).map (fun q =>
    if q.1.parent == "" then { q.1 with parent := "" } else q.1) at hb
  obtain ⟨q, hq, hqb⟩ := List.mem_map.mp hb
  obtain ⟨hzip, hkeep⟩ := List.mem_filter.mp hq
  have hbm : b.id = q.1.id ∧ b.parent = q.1.parent ∧ b.exclusive = q.1.exclusive := by
    rw [← hqb]
    by_cases hp : q.1.parent = "" <;> simp [hp]
  obtain ⟨hid, hparent, hexcl⟩ := hbm
  refine ⟨q.1, List.fst_mem_of_mem_zipIdx hzip, hkeep, ?_⟩
  rw [← hbx]
  by_cases hroot : q.1.id = root
  · simp [hid, hexcl, hroot]
  · simp [hid, hparent, hexcl, hroot]

private theorem noteSelection_box_fields {inp : Input} {keep : ModelBox → Bool}
    {root : String} {scene : Scene} {a : ModelBox} {b : Box}
    (hnd : (inp.boxes.map (·.id)).Nodup)
    (hsource : NoteSelectionBoxSources inp keep root scene)
    (ha : a ∈ inp.boxes) (hb : b ∈ scene.boxes) (hid : b.id = a.id) :
    keep a = true ∧ b.exclusive = a.exclusive ∧
      b.parent = (if a.id == root then "" else a.parent) := by
  obtain ⟨x, hx, hbx, hbp, hbe⟩ := hsource b hb
  obtain ⟨src, hsrc, hk, hxs, hxe, hxp⟩ := noteSubInput_box_source hx
  have heq : src = a := eq_of_mem_id hnd hsrc ha (hxs.symm.trans (hbx.symm.trans hid))
  subst src
  exact ⟨hk, hbe.trans hxe, hbp.trans hxp⟩

private theorem notesPart_root_not_sibling {inp : Input} {o : Options} {root : String}
    {a b : ModelBox} (hwf : WellFormed (inputModel inp o))
    (ha : a ∈ inp.boxes) (hb : b ∈ inp.boxes)
    (hne : a.id ≠ b.id) (hpar : a.parent = b.parent)
    (hkeep : (b.id == root || Compound.inside inp.boxes root b.id) = true) :
    a.id ≠ root := by
  intro haroot
  have hinside := (Bool.or_eq_true_iff.mp hkeep).resolve_left fun hr =>
    hne (haroot.trans (beq_iff_eq.mp hr).symm)
  obtain ⟨member, hmember, hmid, i, _, ancestor, hget, haid, hi⟩ := inside_spec hinside
  have hnd := Model.boxIds_nodup hwf
  have hmEq : member = b := eq_of_mem_id hnd hmember hb hmid
  have haEq : ancestor = a :=
    eq_of_mem_id hnd (getElem?_mem' hget) ha (haid.trans haroot.symm)
  rw [haEq] at hget
  obtain ⟨_, hgetB⟩ := List.mem_iff_getElem?.mp hb
  have hpath : i ∈ Compound.path inp.boxes b := by
    change i ∈ Compound.ancestors inp.boxes inp.boxes.length b.parent
    rw [← hmEq]
    exact hi
  have hprefix : (Compound.path inp.boxes a ++ [i]) <+: Compound.path inp.boxes b :=
    Compound.path_ancestor_prefix (inputModel inp o) hwf hget hgetB hpath
  obtain ⟨_, heq⟩ := hprefix
  have hpaths : Compound.path inp.boxes a = Compound.path inp.boxes b :=
    congrArg (Compound.ancestors inp.boxes inp.boxes.length) hpar
  have hlen := congrArg List.length heq
  simp only [List.length_append, List.length_singleton, hpaths] at hlen
  omega

/-- Distinct exclusive input siblings in the same executed fragment have disjoint
rectangles. A note selection has only one id. In a part selection, a distinct
partner of the root would be its descendant, whose ancestor path is strictly
longer, whereas input siblings have the same ancestor path. Thus neither box
of a part pair lost its parent, and the executed part's C2 applies. -/
theorem notesPlacedFragmentSiblings_disjoint
    {inp : Input} {o : Options} {margin : Int} {contracted : Scene}
    {l : BundleLayout} {p : Placed}
    (hwf : WellFormed (inputModel inp o))
    (hp : p ∈ placedOf' margin contracted l)
    (hPart : NoteSelectionBoxSources inp
      (fun x => x.id == l.top.id || Compound.inside inp.boxes l.top.id x.id)
      l.top.id l.part.scene)
    (hNotes : ∀ q ∈ l.notes,
      NoteSelectionBoxSources inp (fun x => x.id == q.1.id) q.1.id q.2.scene)
    (hC2 : Validator.C2 l.part.scene.layoutDump)
    {a b : ModelBox} {sa sb : Box}
    (ha : a ∈ inp.boxes) (hb : b ∈ inp.boxes)
    (hsa : sa ∈ p.scene.boxes) (hsb : sb ∈ p.scene.boxes)
    (haid : sa.id = a.id) (hbid : sb.id = b.id) (hne : sa.id ≠ sb.id)
    (hea : a.exclusive = true) (heb : b.exclusive = true) (hpar : a.parent = b.parent) :
    Disjoint sa.rect sb.rect := by
  have hnd := Model.boxIds_nodup hwf
  rcases placedOf_scene hp with hscene | ⟨q, hq, hscene⟩
  · rw [hscene] at hsa hsb
    obtain ⟨hka, hexa, hpa⟩ := noteSelection_box_fields hnd hPart ha hsa haid
    obtain ⟨hkb, hexb, hpb⟩ := noteSelection_box_fields hnd hPart hb hsb hbid
    have hids : a.id ≠ b.id := fun h => hne (haid.trans (h.trans hbid.symm))
    have haroot := notesPart_root_not_sibling hwf ha hb hids hpar hkb
    have hbroot := notesPart_root_not_sibling hwf hb ha (Ne.symm hids) hpar.symm hka
    have hpa' : sa.parent = a.parent := by simpa [haroot] using hpa
    have hpb' : sb.parent = b.parent := by simpa [hbroot] using hpb
    exact hC2 sa hsa sb hsb hne (hexa.trans hea) (hexb.trans heb)
      (hpa'.trans (hpar.trans hpb'.symm))
  · rw [hscene] at hsa hsb
    have hqa : a.id = q.1.id := beq_iff_eq.mp
      (noteSelection_box_fields hnd (hNotes q hq) ha hsa haid).1
    have hqb : b.id = q.1.id := beq_iff_eq.mp
      (noteSelection_box_fields hnd (hNotes q hq) hb hsb hbid).1
    exact (hne ((haid.trans hqa).trans (hbid.trans hqb).symm)).elim

end Elegant.Layered.PipelineImpl
