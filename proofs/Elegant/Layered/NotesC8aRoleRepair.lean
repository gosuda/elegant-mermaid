import Elegant.Layered.NotesFlatLabelClauses

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Repair of the C8a contracted-role residual.

Witness of falsity: on the group-note probe input
`[{id := G, role := .group}, {id := C1, parent := G}, {id := G.note, ...}]`
the contracted scene is `[(G, node)]`, so `NotesC8aContractRole` fails:
no input box has id `G` with role id `"node"`. The cause is `contractOne`,
which rewrites the bundle top to `{ role := .node, direction := "" }`.
Hence the unconditional contracted-scene role mirror is FALSE in general:
any base returning a box whose id is absent from the input also falsifies
it, so it is not a structural fact of `contractOne`.

True form: a contracted box either keeps its input role, or it is a bundle
top whose input role is group and whose contracted role is node. The
fold-level membership form below IS structural (proved by induction on
`layouts` from the `contractOne` definition, no base facts needed); the
contracted-scene form follows with one extra mirror premise (contracted
roles match folded roles), which holds on both assembly probe inputs and
follows for `layoutX` from its box-role preservation.

Consumer replacement: in `NotesC8aGeom` (consumed as
`NotesFlatFacts.c8aGeom`), replace the `NotesC8aContractRole e` conjunct
with `NotesC8aContractRoleT e` below (that is, adopt `NotesC8aGeomT e`),
and call `notes_c8a'` instead of `notes_c8a`.
-/

/-- True contracted-role residual: every contracted box has an input box
with its id, and either the roles agree or the box is a bundle top whose
input role is group while its contracted role is node. -/
def NotesC8aContractRoleT {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ cg ∈ e.contracted.scene.boxes,
    ∃ ib, inp.boxes.find? (fun b => b.id == cg.id) = some ib ∧
      (ib.role.id = cg.role ∨
        ∃ l ∈ e.layouts, l.top.id = cg.id ∧ ib.role.id = "group" ∧ cg.role = "node")

/-- The role-aware C8a context. Fragment id presence rules out a contracted
bundle top as the source of a group frame's rectangle. -/
def NotesC8aGeomT {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC8aTopNodup e ∧ NotesC8aFold e ∧ NotesC8aLen e ∧ NotesC8aContractScene e ∧
    NotesC8aContractRoleT e ∧ NotesC8aFragRole e ∧ NotesC8aFragFound e ∧
    NotesC8aClear e ∧ NotesC8aFragDisj e ∧ NotesC8aSceneAnc e ∧
    NotesC8aEnv e ∧ NotesC8aEnvDisj e

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Find on an id-unique list names the member with that id (prefixed copy:
the `ComposeNotesC8a` helper is private to that module). -/
private theorem ncrr_find?_unique {α : Type} (f : α → String) :
    ∀ (l : List α), (l.map f).Nodup → ∀ (x : α), x ∈ l → ∀ v, f x = v →
      l.find? (fun a => f a == v) = some x := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons c cs ih =>
    intro hnd x hx v hv
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hx with
    | head =>
      simp [hv]
    | tail _ hx' =>
      have hfx : f x ∈ cs.map f := List.mem_map.mpr ⟨x, hx', rfl⟩
      by_cases hcv : (f c == v) = true
      · exact absurd (by
          have hce : f c = v := beq_iff_eq.mp hcv
          rw [show f c = f x from hce.trans hv.symm]
          exact hfx) hnot
      · simp only [List.find?_cons, hcv]
        exact ih hnd' x hx' v hv

/-- Equal images under `f` of two members of a duplicate-free image list
force the members to be equal (prefixed copy). -/
private theorem ncrr_nodup_map_inj_on {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb, e => by
      rw [List.map_cons, List.nodup_cons] at h
      rcases List.mem_cons.mp ha with hax | ha'
      · rcases List.mem_cons.mp hb with hbx | hb'
        · exact hax.trans hbx.symm
        · exfalso
          apply h.1
          rw [← hax, e]
          exact List.mem_map_of_mem hb'
      · rcases List.mem_cons.mp hb with hbx | hb'
        · exfalso
          apply h.1
          rw [← hbx, ← e]
          exact List.mem_map_of_mem ha'
        · exact ncrr_nodup_map_inj_on f xs h.2 ha' hb' e

/-- Rectangles containing a disjoint pair's member stay disjoint (prefixed
copy: the `ComposeNotesC8a` `Disjoint.inner` is private to that module). -/
private theorem ncrr_meetsInterior_contained {i o x : Rect} (hc : o.Contained i)
    (h : i.meetsInterior x) : o.meetsInterior x := by
  unfold Rect.Contained Rect.meetsInterior at *
  omega

private theorem ncrr_disjoint_inner {x o i : Rect} (hd : Disjoint x o) (hc : o.Contained i) :
    Disjoint x i := by
  unfold Disjoint at hd ⊢
  intro hm
  exact hd ((Rect.meetsInterior_comm o x).mp
    (ncrr_meetsInterior_contained hc ((Rect.meetsInterior_comm x i).mp hm)))

/-- `Disjoint` survives a common translation (prefixed copy: the
`ComposeNotesC8a` helper is private to that module). -/
private theorem ncrr_disjoint_shiftRect (a b : Rect) (dx dy : Int) :
    Disjoint (shiftRect dx dy a) (shiftRect dx dy b) ↔ Disjoint a b := by
  simp only [Disjoint, Rect.meetsInterior, shiftRect]
  constructor <;> intro h <;> omega

/-- Shifting preserves strict containment (prefixed copy: the sibling
`nlc_strictInside_shift` is private to its module). -/
private theorem ncrr_strictInside_shift (o i : Rect) (dx dy : Int) :
    (shiftRect dx dy o).StrictInside (shiftRect dx dy i) ↔ o.StrictInside i := by
  simp only [Rect.StrictInside, shiftRect]
  constructor <;> intro h <;> omega

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Ancestor inclusion through one id/parent transfer (prefixed copy). -/
private theorem ncrr_go_mirror {src dst : List Box} (ht : IdParentTransfer src dst) :
    ∀ (k : Nat) (s x : String),
      x ∈ LayoutDump.ancestors.go (⟨⟨0, 0⟩, dst, [], []⟩ : LayoutDump) k s →
      x ∈ LayoutDump.ancestors.go (⟨⟨0, 0⟩, src, [], []⟩ : LayoutDump) k s := by
  intro k
  induction k with
  | zero => intro s x hx; cases hx
  | succ k ih =>
    intro s x hx
    simp only [LayoutDump.ancestors.go, LayoutDump.box?] at hx ⊢
    cases hd : dst.find? (fun b => b.id == s) with
    | none => rw [hd] at hx; cases hx
    | some db =>
      rw [hd] at hx
      obtain ⟨sb, hsf, _, hpar⟩ := ht s db hd
      rw [hsf] at ⊢
      dsimp only at hx ⊢
      rw [← hpar] at hx
      by_cases hp0 : sb.parent = ""
      · simp only [hp0, ↓reduceIte] at hx ⊢
        exact hx
      · simp only [hp0, ↓reduceIte] at hx ⊢
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih sb.parent x hx')

/-- Ancestor inclusion is monotone in fuel (prefixed copy). -/
private theorem ncrr_go_mono {d : LayoutDump} {k k' : Nat} (hle : k ≤ k') {s x : String}
    (hm : x ∈ LayoutDump.ancestors.go d k s) :
    x ∈ LayoutDump.ancestors.go d k' s := by
  induction k' generalizing k s x with
  | zero =>
    have hk : k = 0 := Nat.le_zero.mp hle
    subst hk
    cases hm
  | succ k' ih =>
    cases k with
    | zero => cases hm
    | succ k =>
      have hkk : k ≤ k' := Nat.le_of_succ_le_succ hle
      simp only [LayoutDump.ancestors.go, LayoutDump.box?] at hm ⊢
      cases hd : d.boxes.find? (fun b => b.id == s) with
      | none => rw [hd] at hm; cases hm
      | some b =>
        rw [hd] at hm
        dsimp only at hm ⊢
        by_cases hp : b.parent = ""
        · simp only [hp, ↓reduceIte] at hm ⊢
          exact hm
        · simp only [hp, ↓reduceIte] at hm ⊢
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hkk hm')

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Ancestor walks agree on equal box lists (prefixed copy). -/
private theorem ncrr_ancestors_go_boxes_congr {d₁ d₂ : LayoutDump} (hb : d₁.boxes = d₂.boxes)
    (k : Nat) (s : String) :
    LayoutDump.ancestors.go d₁ k s = LayoutDump.ancestors.go d₂ k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [LayoutDump.ancestors.go]
    have hbx : d₁.box? s = d₂.box? s := by simp only [LayoutDump.box?, hb]
    rw [hbx]
    cases hx : d₂.box? s with
    | none => rfl
    | some b =>
      by_cases hp : b.parent = ""
      · simp only [hp, ↓reduceIte]
      · simp only [hp, ↓reduceIte, ih]

/-- Ancestors agree on equal box lists (prefixed copy). -/
private theorem ncrr_ancestors_boxes_congr {d₁ d₂ : LayoutDump} (hb : d₁.boxes = d₂.boxes)
    (s : String) : d₁.ancestors s = d₂.ancestors s := by
  unfold LayoutDump.ancestors
  rw [hb]
  exact ncrr_ancestors_go_boxes_congr hb d₂.boxes.length s

/-- Contracted-scene ancestors are input ancestors, through the folded-input
transfers and the length bound (the `hsubc` step of the C8a composition). -/
private theorem ncrr_contractedAncestors {inp : Input} {layouts : List BundleLayout}
    {contracted : FamilyResult}
    (hfold : IdParentTransferM inp.boxes
      ((layouts.foldl contractOne inp).boxes.map
        (fun b => Box.mk b.id b.role.id ⟨0, 0, 0, 0⟩ b.parent b.exclusive)))
    (hclen : contracted.scene.boxes.length ≤ inp.boxes.length)
    (hcontractscene : IdParentTransferM ((layouts.foldl contractOne inp).boxes)
      contracted.scene.boxes) :
    ∀ (s x : String), x ∈ contracted.scene.layoutDump.ancestors s →
      x ∈ (inpDumpOf inp).ancestors s := by
  intro s x hx
  rw [ncrr_ancestors_boxes_congr
    (d₂ := ⟨⟨0, 0⟩, contracted.scene.boxes, [], []⟩)
    (show contracted.scene.layoutDump.boxes = contracted.scene.boxes from rfl) s] at hx
  unfold LayoutDump.ancestors at hx ⊢
  have h3 := ncrr_go_mirror hcontractscene contracted.scene.boxes.length s x hx
  have h4 := ncrr_go_mirror hfold contracted.scene.boxes.length s x h3
  have hlen : (inpDumpOf inp).boxes.length = inp.boxes.length :=
    List.length_map _
  rw [hlen]
  exact ncrr_go_mono hclen h4

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- One `contractOne` step keeps every box's input origin: a surviving box
either keeps its input role, or it is the bundle top rewritten from group
to node. This is the structural core of the true role residual. -/
private theorem ncrr_contractOne_role (inp : Input) (l : BundleLayout) :
    ∀ fb ∈ (contractOne inp l).boxes, ∃ ib ∈ inp.boxes, ib.id = fb.id ∧
      (ib.role.id = fb.role.id ∨
        (l.top.id = fb.id ∧ ib.role.id = "group" ∧ fb.role.id = "node")) := by
  intro fb hfb
  simp only [contractOne, List.mem_map, List.mem_filter] at hfb
  obtain ⟨q, hq, hxq⟩ := hfb
  obtain ⟨hz, _⟩ := hq
  obtain ⟨_, hlt, hxeq⟩ := List.mem_zipIdx hz
  have hqmem : q.1 ∈ inp.boxes := by
    have hidx : q.2 - 0 < inp.boxes.length := by omega
    rw [hxeq]
    exact List.getElem_mem hidx
  by_cases heq : (q.1.id == l.top.id) = true
  · have htop : q.1.id = l.top.id := beq_iff_eq.mp heq
    simp only [heq, ↓reduceIte] at hxq
    subst hxq
    refine ⟨q.1, hqmem, rfl, ?_⟩
    cases hr : q.1.role with
    | group =>
      exact Or.inr ⟨htop.symm.trans rfl, rfl, rfl⟩
    | node =>
      exact Or.inl rfl
  · have hfalse : (q.1.id == l.top.id) = false := by
      cases hbb : (q.1.id == l.top.id) with
      | true => exact absurd hbb heq
      | false => rfl
    simp only [hfalse] at hxq
    subst hxq
    exact ⟨q.1, hqmem, rfl, Or.inl rfl⟩

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Folded `contractOne` keeps every box's input origin: a folded box either
keeps its input role, or it is some bundle top rewritten from group to node.
Structural in `layouts` and `inp`; no base facts needed. -/
private theorem ncrr_fold_roleT (inp : Input) (layouts : List BundleLayout) :
    ∀ fb ∈ (layouts.foldl contractOne inp).boxes, ∃ ib ∈ inp.boxes, ib.id = fb.id ∧
      (ib.role.id = fb.role.id ∨
        ∃ l ∈ layouts, l.top.id = fb.id ∧ ib.role.id = "group" ∧ fb.role.id = "node") := by
  induction layouts generalizing inp with
  | nil =>
    intro fb hfb
    simp only [List.foldl_nil] at hfb
    exact ⟨fb, hfb, rfl, Or.inl rfl⟩
  | cons l rest ih =>
    intro fb hfb
    rw [List.foldl_cons] at hfb
    obtain ⟨ib', hib'mem, hib'id, hdisj'⟩ := ih _ fb hfb
    obtain ⟨ib, hibmem, hibid, hdisj⟩ := ncrr_contractOne_role inp l ib' hib'mem
    have hid : ib.id = fb.id := hibid.trans hib'id
    refine ⟨ib, hibmem, hid, ?_⟩
    rcases hdisj with hleft | ⟨htop, hgr, hnode⟩
    · rcases hdisj' with hleft' | ⟨l', hlm', htop', hgr', hnode'⟩
      · exact Or.inl (hleft.trans hleft')
      · exact Or.inr ⟨l', List.mem_cons_of_mem _ hlm', htop',
          hleft.trans hgr', hnode'⟩
    · rcases hdisj' with hleft' | ⟨l', hlm', htop', hgr', hnode'⟩
      · exact Or.inr ⟨l, List.mem_cons_self, htop.trans hib'id, hgr,
          hleft'.symm.trans hnode⟩
      · exfalso
        have hcontra : ("node" : String) = "group" := hnode.symm.trans hgr'
        exact absurd hcontra (by decide)

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- The true contracted-role residual holds for every execution whose
contracted scene mirrors the folded-input roles. The fold fact is discharged
internally by the structural lemma above; the mirror premise is base-specific
(true for `layoutX`) and is probed true on both assembly inputs below. -/
theorem notesC8aContractRoleT_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hnd : (inp.boxes.map (fun b => b.id)).Nodup)
    (hmirror : ∀ cg ∈ e.contracted.scene.boxes, ∃ fb ∈ (e.layouts.foldl contractOne inp).boxes,
      fb.id = cg.id ∧ cg.role = fb.role.id) :
    NotesC8aContractRoleT e := by
  intro cg hcg
  obtain ⟨fb, hfbm, hfbid, hfbrole⟩ := hmirror cg hcg
  obtain ⟨ib, hibmem, hibid, hdisj⟩ := ncrr_fold_roleT inp e.layouts fb hfbm
  have hfind_ib : inp.boxes.find? (fun b => b.id == fb.id) = some ib :=
    ncrr_find?_unique (fun b : ModelBox => b.id) inp.boxes hnd ib hibmem fb.id hibid
  refine ⟨ib, ?_, ?_⟩
  · have hfc : fb.id = cg.id := hfbid
    rw [← hfc]
    exact hfind_ib
  · rcases hdisj with hleft | ⟨l, hlm, htop, hgr, hnode⟩
    · exact Or.inl (hleft.trans hfbrole.symm)
    · exact Or.inr ⟨l, hlm, htop.trans hfbid, hgr, hfbrole.trans hnode⟩

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- C8a, both rects from fragments: same-scene transport, same-bundle
disjointness, or cross-bundle envelopes (the fragment/fragment case of the
composition, replayed under the true role residual). -/
private theorem ncrr_c8a_ff {inp : Input} {margin : Int}
    {layouts : List BundleLayout} {contracted : FamilyResult}
    {placed : List (List Placed)}
    (hp : layouts.mapM (placedFragments margin contracted.scene) = .ok placed)
    (hnd : (inp.boxes.map (fun b => b.id)).Nodup)
    (htopndup : (layouts.map (·.top.id)).Nodup)
    (hfragrole : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∃ ib ∈ inp.boxes, ib.id = sb.id ∧ ib.role.id = sb.role)
    (hfragdisj : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ p' ∈ placedOf' margin contracted.scene l, ∀ sg ∈ p.scene.boxes, ∀ sb ∈ p'.scene.boxes,
      p ≠ p' → sg.id ≠ sb.id →
      Disjoint (shiftRect p.dx p.dy sg.rect) (shiftRect p'.dx p'.dy sb.rect))
    (hsceneAnc : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l, ∀ s x : String,
      x ∈ p.scene.layoutDump.ancestors s → x ∈ (inpDumpOf inp).ancestors s)
    (hsame : ∀ l ∈ layouts, Validator.C8a l.part.scene.layoutDump)
    (hnote : ∀ l ∈ layouts, ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump)
    (henv : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ sb ∈ p.scene.boxes, (envRect contracted.scene l).Contained (shiftRect p.dx p.dy sb.rect))
    (henvdisj : ∀ a ∈ layouts, ∀ b ∈ layouts, a.top.id ≠ b.top.id →
      Disjoint (envRect contracted.scene a) (envRect contracted.scene b))
    {gi bi : ModelBox} (hgimem : gi ∈ inp.boxes)
    {g b : Box} {F : ModelBox → Box}
    (hrole_g : (F gi).role = gi.role.id) (hgif : F gi = g) (grole : g.role = "group")
    (hg1 : gi.id ∉ (inpDumpOf inp).ancestors bi.id)
    (hg2 : bi.id ∉ (inpDumpOf inp).ancestors gi.id) (hne2 : gi.id ≠ bi.id)
    {pg : Placed} (hgpf : pg ∈ placed.flatten)
    {sg : Box} (hsgm : sg ∈ pg.scene.boxes) (hsgid : sg.id = gi.id)
    (hsgshift : shiftRect pg.dx pg.dy sg.rect = g.rect)
    {pb : Placed} (hbpf : pb ∈ placed.flatten)
    {sb : Box} (hsbm : sb ∈ pb.scene.boxes) (hsbid : sb.id = bi.id)
    (hsbshift : shiftRect pb.dx pb.dy sb.rect = b.rect) :
    Disjoint g.rect b.rect := by
  obtain ⟨lg, hlgm, hpgp⟩ := placedFlatten_mem hp hgpf
  obtain ⟨lb, hlbm, hpbp⟩ := placedFlatten_mem hp hbpf
  by_cases hlge : lg = lb
  · subst hlge
    by_cases hpp : pg = pb
    · subst hpp
      have hne3 : sg.id ≠ sb.id := by rw [hsgid, hsbid]; exact hne2
      have hsgrole : sg.role = "group" := by
        obtain ⟨ib, hibm, hibid, hibrole⟩ := hfragrole lg hlgm pg hpgp sg hsgm
        have h1u := ncrr_find?_unique (fun b : ModelBox => b.id) inp.boxes hnd ib hibm gi.id
          (hibid.trans hsgid)
        have h2u := ncrr_find?_unique (fun b : ModelBox => b.id) inp.boxes hnd gi hgimem gi.id rfl
        have hibig : ib = gi := Option.some.inj ((h2u.symm.trans h1u).symm)
        rw [← hibrole, hibig, ← hrole_g, hgif, grole]
      have hA' : sg.id ∉ pg.scene.layoutDump.ancestors sb.id := by
        intro hm
        exact hg1 (by rw [← hsgid, ← hsbid]; exact hsceneAnc lg hlgm pg hpgp sb.id sg.id hm)
      have hB' : sb.id ∉ pg.scene.layoutDump.ancestors sg.id := by
        intro hm
        exact hg2 (by rw [← hsbid, ← hsgid]; exact hsceneAnc lg hlgm pg hpgp sg.id sb.id hm)
      rw [← hsgshift, ← hsbshift]
      refine (ncrr_disjoint_shiftRect _ _ _ _).mpr ?_
      rcases placedOf_scene hpgp with hps | ⟨q, hqm, hqs⟩
      · rw [hps] at hsgm hsbm hA' hB'
        exact hsame lg hlgm sg hsgm hsgrole sb hsbm (Ne.symm hne3) hA' hB'
      · rw [hqs] at hsgm hsbm hA' hB'
        exact hnote lg hlgm q hqm sg hsgm hsgrole sb hsbm (Ne.symm hne3) hA' hB'
    · have hne3 : sg.id ≠ sb.id := by rw [hsgid, hsbid]; exact hne2
      have hd := hfragdisj lg hlgm pg hpgp pb hpbp sg hsgm sb hsbm hpp hne3
      rw [← hsgshift, ← hsbshift]
      exact hd
  · have htopne : lg.top.id ≠ lb.top.id := fun heq =>
      hlge (ncrr_nodup_map_inj_on (fun l : BundleLayout => l.top.id) layouts htopndup hlgm hlbm heq)
    have hd := henvdisj lg hlgm lb hlbm htopne
    have h1' := henv lg hlgm pg hpgp sg hsgm
    have h2' := henv lb hlbm pb hpbp sb hsbm
    rw [hsgshift] at h1'
    rw [hsbshift] at h2'
    have hd1 : Disjoint (envRect contracted.scene lg) b.rect :=
      ncrr_disjoint_inner hd h2'
    have hd2 : Disjoint b.rect (envRect contracted.scene lg) :=
      (Disjoint.comm _ _).mp hd1
    have hd3 : Disjoint b.rect g.rect := ncrr_disjoint_inner hd2 h1'
    exact (Disjoint.comm _ _).mp hd3

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Mixed clearance with the fragment as the output group. -/
private theorem ncrr_c8a_fc {inp : Input} {margin : Int}
    {layouts : List BundleLayout} {contracted : FamilyResult}
    {fragments : List Placed}
    (hclear : MixedNotesC8aClear inp margin contracted.scene layouts fragments)
    {gi bi : ModelBox} (hgimem : gi ∈ inp.boxes) (hgroup : gi.role.id = "group")
    (hg1 : gi.id ∉ (inpDumpOf inp).ancestors bi.id)
    (hg2 : bi.id ∉ (inpDumpOf inp).ancestors gi.id) (hne : gi.id ≠ bi.id)
    {g b : Box} {lg : BundleLayout} (hlgm : lg ∈ layouts)
    {pg : Placed} (hpgp : pg ∈ placedOf' margin contracted.scene lg)
    {sg : Box} (hsgm : sg ∈ pg.scene.boxes) (hsgid : sg.id = gi.id)
    (hsgshift : shiftRect pg.dx pg.dy sg.rect = g.rect)
    {cb : Box} (hcbmem : cb ∈ contracted.scene.boxes)
    (hcbid : cb.id = bi.id) (hcbr : cb.rect = b.rect)
    (hnotfB : ∀ p ∈ fragments, ∀ q : Rect, p.rect bi.id ≠ some q) :
    Disjoint g.rect b.rect := by
  have hdd := MixedNotesC8aClear.ofIds hclear hlgm hpgp hsgm hcbmem hsgid hcbid
    hnotfB hne hg1 hg2 ⟨gi, hgimem, hgroup, Or.inl rfl⟩
  simpa only [hsgshift, hcbr] using hdd

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Mixed clearance with the contracted rectangle as the output group. -/
private theorem ncrr_c8a_cf {inp : Input} {margin : Int}
    {layouts : List BundleLayout} {contracted : FamilyResult}
    {fragments : List Placed}
    (hclear : MixedNotesC8aClear inp margin contracted.scene layouts fragments)
    {gi bi : ModelBox} (hgimem : gi ∈ inp.boxes) (hgroup : gi.role.id = "group")
    (hg1 : gi.id ∉ (inpDumpOf inp).ancestors bi.id)
    (hg2 : bi.id ∉ (inpDumpOf inp).ancestors gi.id) (hne : gi.id ≠ bi.id)
    {g b : Box} {lb : BundleLayout} (hlbm : lb ∈ layouts)
    {pb : Placed} (hpbp : pb ∈ placedOf' margin contracted.scene lb)
    {sb : Box} (hsbm : sb ∈ pb.scene.boxes) (hsbid : sb.id = bi.id)
    (hsbshift : shiftRect pb.dx pb.dy sb.rect = b.rect)
    {cg : Box} (hcgmem : cg ∈ contracted.scene.boxes)
    (hcgid : cg.id = gi.id) (hcgr : cg.rect = g.rect)
    (hnotfG : ∀ p ∈ fragments, ∀ q : Rect, p.rect gi.id ≠ some q) :
    Disjoint g.rect b.rect := by
  have hdd := MixedNotesC8aClear.ofIds hclear hlbm hpbp hsbm hcgmem hsbid hcgid
    hnotfG hne.symm hg2 hg1 ⟨gi, hgimem, hgroup, Or.inr rfl⟩
  exact (Rect.disjoint_comm _ _).mpr (by simpa only [hsbshift, hcgr] using hdd)

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- A bundle top always has a fragment rect: its id is a fragment id, so the
fragment-found residual places a box with that id, which yields a rect. This
kills the bundle-top alternative of the true role residual in the
both-contracted case. -/
private theorem ncrr_bundleTop_hasRect {inp : Input} {margin : Int}
    {layouts : List BundleLayout} {contracted : FamilyResult}
    {placed : List (List Placed)}
    (hp : layouts.mapM (placedFragments margin contracted.scene) = .ok placed)
    (hfragfound : ∀ l ∈ layouts, ∀ id : String, fragmentIdOf inp l id = true →
      (placedOf' margin contracted.scene l).any
        (fun p => p.scene.boxes.any (fun b => b.id == id)) = true)
    {gi : ModelBox} {l : BundleLayout} (hlm : l ∈ layouts) (htopid : l.top.id = gi.id)
    (hnotfG : ∀ p ∈ placed.flatten, ∀ q : Rect, p.rect gi.id ≠ some q) :
    False := by
  have hfrag : fragmentIdOf inp l gi.id = true := by
    unfold fragmentIdOf
    have heq : (gi.id == l.top.id) = true := by
      rw [htopid.symm]; exact beq_self_eq_true _
    simp only [heq, Bool.true_or]
  obtain ⟨p, hpm, hsbany⟩ := List.any_eq_true.mp (hfragfound l hlm gi.id hfrag)
  have hfnd : p.scene.boxes.find? (fun x => x.id == gi.id) ≠ none := by
    intro hfnd0
    rw [List.find?_eq_none] at hfnd0
    obtain ⟨bx, hbxmem, hbxany⟩ := List.any_eq_true.mp hsbany
    exact absurd hbxany (hfnd0 bx hbxmem)
  have hpR : ∃ q : Rect, p.rect gi.id = some q := by
    simp only [Placed.rect]
    cases hfnd' : p.scene.boxes.find? (fun x => x.id == gi.id) with
    | none => exact absurd hfnd' hfnd
    | some _ => exact ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hpR
  exact absurd hq (hnotfG p (placedOf_mem_flatten hp hlm hpm) q)

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- C8a, both rects contracted: with role agreement the contracted scene's C8a
applies; a bundle top with node role cannot occur (it always has a fragment
rect). The new bundle-top alternative is discharged by impossibility. -/
private theorem ncrr_c8a_cc {inp : Input} {margin : Int}
    {layouts : List BundleLayout} {contracted : FamilyResult}
    {placed : List (List Placed)}
    (hp : layouts.mapM (placedFragments margin contracted.scene) = .ok placed)
    (hnd : (inp.boxes.map (fun b => b.id)).Nodup)
    (hcontract : Validator.C8a contracted.scene.layoutDump)
    (hsubc : ∀ (s x : String), x ∈ contracted.scene.layoutDump.ancestors s →
      x ∈ (inpDumpOf inp).ancestors s)
    (hfragfound : ∀ l ∈ layouts, ∀ id : String, fragmentIdOf inp l id = true →
      (placedOf' margin contracted.scene l).any
        (fun p => p.scene.boxes.any (fun b => b.id == id)) = true)
    {gi bi : ModelBox} (hgimem : gi ∈ inp.boxes)
    {g b : Box} {F : ModelBox → Box}
    (hrole_g : (F gi).role = gi.role.id) (hgif : F gi = g) (grole : g.role = "group")
    (hg1 : gi.id ∉ (inpDumpOf inp).ancestors bi.id)
    (hg2 : bi.id ∉ (inpDumpOf inp).ancestors gi.id) (hne2 : gi.id ≠ bi.id)
    {cg : Box} (hcgmem : cg ∈ contracted.scene.boxes)
    (hcgid : cg.id = gi.id) (hcgr : cg.rect = g.rect)
    (hnotfG : ∀ p ∈ placed.flatten, ∀ q : Rect, p.rect gi.id ≠ some q)
    (hroleT : ∃ ib, inp.boxes.find? (fun b => b.id == cg.id) = some ib ∧
      (ib.role.id = cg.role ∨
        ∃ l ∈ layouts, l.top.id = cg.id ∧ ib.role.id = "group" ∧ cg.role = "node"))
    {cb : Box} (hcbmem : cb ∈ contracted.scene.boxes)
    (hcbid : cb.id = bi.id) (hcbr : cb.rect = b.rect) :
    Disjoint g.rect b.rect := by
  have hgirole : gi.role.id = "group" := by rw [← hrole_g, hgif, grole]
  obtain ⟨ibg, hibgf, hdisj⟩ := hroleT
  rw [hcgid] at hibgf
  have hibgig : gi = ibg := Option.some.inj
    (((ncrr_find?_unique (fun b : ModelBox => b.id) inp.boxes hnd gi hgimem gi.id rfl).symm.trans
      hibgf))
  rcases hdisj with hleft | ⟨l, hlm, htop, hgr, hnode⟩
  · have hcgrole : cg.role = "group" := by
      rw [← hleft, ← hibgig]; exact hgirole
    have hneAB : cb.id ≠ cg.id := fun hc0 =>
      (Ne.symm hne2) (hcbid.symm.trans (hc0.trans hcgid))
    have hA : cg.id ∉ contracted.scene.layoutDump.ancestors cb.id := by
      intro hm
      rw [hcgid, hcbid] at hm
      exact hg1 (hsubc bi.id gi.id hm)
    have hB : cb.id ∉ contracted.scene.layoutDump.ancestors cg.id := by
      intro hm
      rw [hcgid, hcbid] at hm
      exact hg2 (hsubc gi.id bi.id hm)
    have hdd := hcontract cg hcgmem hcgrole cb hcbmem hneAB hA hB
    rw [hcgr, hcbr] at hdd
    exact hdd
  · exfalso
    exact ncrr_bundleTop_hasRect hp hfragfound hlm (htop.trans hcgid) hnotfG

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Bundle composition preserves C8a under the true role residual: the replay
of `composeNotes_c8a` with `NotesC8aContractRoleT`. The only changed case is
both-contracted, where role agreement transports the contracted fact and the
bundle-top alternative is impossible (`ncrr_bundleTop_hasRect`). -/
private theorem ncrr_composeNotes_c8aT
    {P : Params} {inp : Input} {o : Options} {margin : Int}
    {lines : List (List Measure.Line)} {contracted : FamilyResult}
    {layouts : List BundleLayout} {atts : List Attach} {scene : Scene}
    (h : composeNotes P inp o margin lines contracted layouts atts = .ok scene)
    (hnd : (inp.boxes.map (fun b => b.id)).Nodup)
    (htopndup : (layouts.map (·.top.id)).Nodup)
    (hcontract : Validator.C8a contracted.scene.layoutDump)
    (hfold : IdParentTransferM inp.boxes
      ((layouts.foldl contractOne inp).boxes.map
        (fun b => Box.mk b.id b.role.id ⟨0, 0, 0, 0⟩ b.parent b.exclusive)))
    (hclen : contracted.scene.boxes.length ≤ inp.boxes.length)
    (hcontractscene : IdParentTransferM ((layouts.foldl contractOne inp).boxes)
      contracted.scene.boxes)
    (hcontractroleT : ∀ cg ∈ contracted.scene.boxes,
      ∃ ib, inp.boxes.find? (fun b => b.id == cg.id) = some ib ∧
      (ib.role.id = cg.role ∨ ∃ l ∈ layouts, l.top.id = cg.id ∧
        ib.role.id = "group" ∧ cg.role = "node"))
    (hfragrole : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∃ ib ∈ inp.boxes, ib.id = sb.id ∧ ib.role.id = sb.role)
    (hfragfound : ∀ l ∈ layouts, ∀ id : String, fragmentIdOf inp l id = true →
      (placedOf' margin contracted.scene l).any
        (fun p => p.scene.boxes.any (fun b => b.id == id)) = true)
    (hclear : ∀ {placed : List (List Placed)},
      layouts.mapM (placedFragments margin contracted.scene) = .ok placed →
      MixedNotesC8aClear inp margin contracted.scene layouts placed.flatten)
    (hfragdisj : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ p' ∈ placedOf' margin contracted.scene l, ∀ sg ∈ p.scene.boxes, ∀ sb ∈ p'.scene.boxes,
        p ≠ p' → sg.id ≠ sb.id →
        Disjoint (shiftRect p.dx p.dy sg.rect) (shiftRect p'.dx p'.dy sb.rect))
    (hsceneAnc : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l, ∀ s x : String,
      x ∈ p.scene.layoutDump.ancestors s → x ∈ (inpDumpOf inp).ancestors s)
    (hsame : ∀ l ∈ layouts, Validator.C8a l.part.scene.layoutDump)
    (hnote : ∀ l ∈ layouts, ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump)
    (henv : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ sb ∈ p.scene.boxes, (envRect contracted.scene l).Contained (shiftRect p.dx p.dy sb.rect))
    (henvdisj : ∀ a ∈ layouts, ∀ b ∈ layouts, a.top.id ≠ b.top.id →
      Disjoint (envRect contracted.scene a) (envRect contracted.scene b)) :
    Validator.C8a scene.layoutDump := by
  obtain ⟨placed, hp, F, hFmem, hFboxes⟩ := composeNotes_boxes h
  have hsubc := ncrr_contractedAncestors hfold hclen hcontractscene
  intro g hg grole b hb gidne hg1 hg2
  rw [composeNotes_ancestors_eq h] at hg1 hg2
  obtain ⟨jg, hjg⟩ := List.mem_iff_getElem?.mp hg
  rw [hFboxes, List.getElem?_map, Option.map_eq_some_iff] at hjg
  obtain ⟨gi, hgi, hgif⟩ := hjg
  have hgimem : gi ∈ inp.boxes := by
    obtain ⟨hb0, hbe⟩ := List.getElem?_eq_some_iff.mp hgi
    rw [← hbe]
    exact List.getElem_mem hb0
  obtain ⟨jb, hjb⟩ := List.mem_iff_getElem?.mp hb
  rw [hFboxes, List.getElem?_map, Option.map_eq_some_iff] at hjb
  obtain ⟨bi, hbi, hbif⟩ := hjb
  have hbimem : bi ∈ inp.boxes := by
    obtain ⟨hb0, hbe⟩ := List.getElem?_eq_some_iff.mp hbi
    rw [← hbe]
    exact List.getElem_mem hb0
  have hgid : g.id = gi.id := by
    rw [← hgif]
    exact (outBox_ok_fields (hFmem gi hgimem)).1
  have hbid : b.id = bi.id := by
    rw [← hbif]
    exact (outBox_ok_fields (hFmem bi hbimem)).1
  rw [hgid, hbid] at hg1 hg2 gidne
  have hrole_g : (F gi).role = gi.role.id := (outBox_ok_fields (hFmem gi hgimem)).2.1
  have hgrouprole : gi.role.id = "group" := by rw [← hrole_g, hgif, grole]
  have hrect_g : outRect placed contracted.scene gi.id = some g.rect := by
    rw [← hgif]
    exact (outBox_ok_fields (hFmem gi hgimem)).2.2.2.2
  have hrect_b : outRect placed contracted.scene bi.id = some b.rect := by
    rw [← hbif]
    exact (outBox_ok_fields (hFmem bi hbimem)).2.2.2.2
  have hne2 : gi.id ≠ bi.id := Ne.symm gidne
  rcases classifyRect hrect_g with hgfrag | ⟨hnotfG, cg, hcgmem, hcgid, hcgr⟩
  · obtain ⟨pg, hgpf, sg, hsgm, hsgid, hsgshift⟩ :
        ∃ pg ∈ placed.flatten, ∃ sg ∈ pg.scene.boxes, sg.id = gi.id ∧
          shiftRect pg.dx pg.dy sg.rect = g.rect := by
      obtain ⟨p, hpf, hpR⟩ := hgfrag
      obtain ⟨sg, hsgm, hsgid, hshift⟩ := Placed.rect_scene_box hpR
      exact ⟨p, hpf, sg, hsgm, hsgid, hshift⟩
    obtain ⟨lg, hlgm, hpgp⟩ := placedFlatten_mem hp hgpf
    rcases classifyRect hrect_b with hbfrag | ⟨hnotfB, cb, hcbmem, hcbid, hcbr⟩
    · obtain ⟨pb, hbpf, sb, hsbm, hsbid, hsbshift⟩ :
          ∃ pb ∈ placed.flatten, ∃ sb ∈ pb.scene.boxes, sb.id = bi.id ∧
            shiftRect pb.dx pb.dy sb.rect = b.rect := by
        obtain ⟨p, hpf, hpR⟩ := hbfrag
        obtain ⟨sb, hsbm, hsbid, hshift⟩ := Placed.rect_scene_box hpR
        exact ⟨p, hpf, sb, hsbm, hsbid, hshift⟩
      exact ncrr_c8a_ff hp hnd htopndup hfragrole hfragdisj hsceneAnc hsame hnote henv
        henvdisj hgimem hrole_g hgif grole hg1 hg2 hne2 hgpf hsgm hsgid hsgshift hbpf
        hsbm hsbid hsbshift
    · exact ncrr_c8a_fc (hclear hp) hgimem hgrouprole hg1 hg2 hne2
        hlgm hpgp hsgm hsgid hsgshift hcbmem hcbid hcbr hnotfB
  · rcases classifyRect hrect_b with hbfrag | ⟨hnotfB, cb, hcbmem, hcbid, hcbr⟩
    · obtain ⟨pb, hbpf, sb, hsbm, hsbid, hsbshift⟩ :
          ∃ pb ∈ placed.flatten, ∃ sb ∈ pb.scene.boxes, sb.id = bi.id ∧
            shiftRect pb.dx pb.dy sb.rect = b.rect := by
        obtain ⟨p, hpf, hpR⟩ := hbfrag
        obtain ⟨sb, hsbm, hsbid, hshift⟩ := Placed.rect_scene_box hpR
        exact ⟨p, hpf, sb, hsbm, hsbid, hshift⟩
      obtain ⟨lb, hlbm, hpbp⟩ := placedFlatten_mem hp hbpf
      exact ncrr_c8a_cf (hclear hp) hgimem hgrouprole hg1 hg2 hne2
        hlbm hpbp hsbm hsbid hsbshift hcgmem hcgid hcgr hnotfG
    · exact ncrr_c8a_cc hp hnd hcontract hsubc hfragfound hgimem hrole_g hgif grole hg1
        hg2 hne2 hcgmem hcgid hcgr hnotfG (hcontractroleT cg hcgmem) hcbmem hcbid hcbr

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- C8a for the note stage under the true role residual: the same composition
as `notes_c8a`, with the role conjunct replaced by `NotesC8aContractRoleT`.
In the new bundle-top case the contracted box has role node, so it is not a
C8a frame of the contracted scene; the output group frame is the note base's
own input box, whose rect comes from its fragment. -/
theorem notes_c8a' {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hBase : Validator.C8a e.contracted.scene.layoutDump)
    (hFragP : ∀ l ∈ e.layouts, Validator.C8a l.part.scene.layoutDump)
    (hFragN : ∀ l ∈ e.layouts, ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump)
    (hGeomT : NotesC8aGeomT e) :
    Validator.C8a res.scene.layoutDump := by
  obtain ⟨htop, hfold, hlen, hcs, hcrT, hfr, hff, hclr, hfd, hsa, henv, henvd⟩ := hGeomT
  exact ncrr_composeNotes_c8aT e.scene_eq (Model.boxIds_nodup hwf) htop hBase hfold hlen hcs
    hcrT hfr hff (fun {placed} hp => NotesC8aClear.forPlaced hclr (placed := placed) hp)
    hfd hsa hFragP hFragN henv henvd

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Probe inputs: the two assembly-probe inputs plus degenerate bundle shapes
(solo node with note, bare group top, empty input, two notes on one node). -/
private def ncrrOpts : Options :=
  { profile := .vector, thoroughness := 3, maxWidth := 0, direction := .TB,
    limits := { maxNodes := 2000, maxEdges := 5000, maxTextBytes := 1048576 }, config := [] }

private def ncrrState : Input :=
  { kind := "state",
    boxes := [{ id := "S1" }, { id := "S2" },
      { id := "S1.note", shape := "note", direction := "right" }],
    routes := [{ id := "R1", fromId := "S1", toId := "S2" },
      { id := "R2", fromId := "S2", toId := "S2" }],
    texts := [], edges := [] }

private def ncrrGroup : Input :=
  { kind := "state",
    boxes := [{ id := "G", role := .group }, { id := "C1", parent := "G" },
      { id := "G.note", shape := "note", direction := "left" }],
    routes := [{ id := "R2", fromId := "C1", toId := "G" }],
    texts := [], edges := [] }

private def ncrrSolo : Input :=
  { kind := "state",
    boxes := [{ id := "S1" },
      { id := "S1.note", shape := "note", direction := "right" }],
    routes := [], texts := [], edges := [] }

private def ncrrBareGroup : Input :=
  { kind := "state",
    boxes := [{ id := "G", role := .group },
      { id := "G.note", shape := "note", direction := "left" }],
    routes := [], texts := [], edges := [] }

private def ncrrEmpty : Input :=
  { kind := "state", boxes := [], routes := [], texts := [], edges := [] }

private def ncrrTwoNotes : Input :=
  { kind := "state",
    boxes := [{ id := "S1" },
      { id := "S1.note", shape := "note", direction := "right" },
      { id := "S1.memo", shape := "note", direction := "left" }],
    routes := [], texts := [], edges := [] }

/-- Replay of the assembly-probe phases on one input. -/
private def ncrrPhases (inp : Input) :
    Except LayoutError (FamilyResult × FamilyResult × List BundleLayout × List (List Placed) × List Placed) := do
  let P ← checkedParams ncrrOpts.profile inp.kind
  let margin := P.canvasMargin
  let gap := 2 * P.slot + 2
  let atts := attachmentsOf inp.boxes
  let bundles := bundlesOf inp.boxes atts
  let layouts ← bundles.mapM
    (bundleLayout (layoutNotes layoutX [] 0) (layoutX []) inp ncrrOpts margin gap)
  let contractedInput := layouts.foldl contractOne inp
  let contracted ← (layoutX []) contractedInput ncrrOpts
  let placed ← layouts.mapM (placedFragments margin contracted.scene)
  pure (← layoutNotes layoutX [] 1 inp ncrrOpts, contracted, layouts, placed, placed.flatten)

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Indexed pairs over placed fragments. -/
private def ncrrIdx (xs : List Placed) : List (Nat × Placed) :=
  (List.range xs.length).zip xs

/-- Bool mirror of `NotesC8aGeomT` plus the old role check and the mirror
premise, on one executed input. -/
private def ncrrGeomTBool (name : String) (inp : Input) : String :=
  match ncrrPhases inp with
  | .error e => name ++ ": ERROR " ++ toString (repr e)
  | .ok (_, contracted, layouts, placed, fragments) =>
    let margin := match checkedParams ncrrOpts.profile inp.kind with
      | .ok P => P.canvasMargin | .error _ => 0
    let inpIds := inp.boxes.map (·.id)
    let transfer (src : List Box) (dst : List Box) : Bool :=
      ((dst.map (·.id)).eraseDups.all fun s =>
        match dst.find? (fun b => b.id == s) with
        | none => true
        | some db => match src.find? (fun b => b.id == s) with
          | none => false
          | some sb => sb.id == db.id && sb.parent == db.parent)
    let folded := (layouts.foldl contractOne inp).boxes.map
      (fun b => Box.mk b.id b.role.id ⟨0, 0, 0, 0⟩ b.parent b.exclusive)
    let foldedRaw := (layouts.foldl contractOne inp).boxes
    let aTopNodup := decide ((layouts.map (·.top.id)).Nodup)
    let aFold := transfer (modelBoxesToDump inp.boxes) folded
    let aLen := decide (contracted.scene.boxes.length ≤ inp.boxes.length)
    let aSceneReal := transfer
      (modelBoxesToDump (layouts.foldl contractOne inp).boxes) contracted.scene.boxes
    let aCRole := contracted.scene.boxes.all fun cg =>
      match inp.boxes.find? (fun b => b.id == cg.id) with
      | some ib => ib.role.id == cg.role
      | none => false
    let aRoleT := contracted.scene.boxes.all fun cg =>
      match inp.boxes.find? (fun b => b.id == cg.id) with
      | some ib => (ib.role.id == cg.role) ||
          layouts.any (fun l => (l.top.id == cg.id) && (ib.role.id == "group") &&
            (cg.role == "node"))
      | none => false
    let aMirror := contracted.scene.boxes.all fun cg =>
      foldedRaw.any fun fb => (fb.id == cg.id) && (cg.role == fb.role.id)
    let aFRole := layouts.all fun l =>
      (placedOf' margin contracted.scene l).all fun p =>
        p.scene.boxes.all fun sb =>
          inp.boxes.any fun ib => ib.id == sb.id && ib.role.id == sb.role
    let aFound := layouts.all fun l =>
      inpIds.all fun id => !(fragmentIdOf inp l id) ||
        ((placedOf' margin contracted.scene l).any fun p =>
          p.scene.boxes.any fun b => b.id == id)
    let aClear := layouts.all fun l =>
      (placedOf' margin contracted.scene l).all fun p =>
        p.scene.boxes.all fun sb =>
          contracted.scene.boxes.all fun cb =>
            (fragments.any fun q => (q.rect cb.id).isSome) ||
              (sb.id == cb.id) || ((inpDumpOf inp).ancestors cb.id).contains sb.id ||
              ((inpDumpOf inp).ancestors sb.id).contains cb.id ||
              !(inp.boxes.any fun ib => ib.role.id == "group" &&
                (ib.id == sb.id || ib.id == cb.id)) ||
              decide (Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect)
    let aFDisj := layouts.all fun l =>
      (ncrrIdx (placedOf' margin contracted.scene l)).all fun (i, p) =>
        (ncrrIdx (placedOf' margin contracted.scene l)).all fun (j, pp) => i == j ||
          (p.scene.boxes.all fun sg => pp.scene.boxes.all fun sb =>
            (sg.id == sb.id) || decide (Disjoint (shiftRect p.dx p.dy sg.rect)
              (shiftRect pp.dx pp.dy sb.rect)))
    let aSAnc := layouts.all fun l =>
      (placedOf' margin contracted.scene l).all fun p =>
        ((p.scene.layoutDump.boxes.map (·.id)) ++ inpIds).all fun s =>
          ((p.scene.layoutDump.ancestors s).all fun x =>
            (((inpDumpOf inp).ancestors s).contains x))
    let aEnv := layouts.all fun l =>
      (placedOf' margin contracted.scene l).all fun p =>
        p.scene.boxes.all fun sb =>
          decide ((envRect contracted.scene l).Contained (shiftRect p.dx p.dy sb.rect))
    let aEnvDisj := layouts.all fun a => layouts.all fun b =>
      (a.top.id == b.top.id) ||
        decide (Disjoint (envRect contracted.scene a) (envRect contracted.scene b))
    let _ := placed
    name ++ ": topNodup=" ++ toString aTopNodup ++ " fold=" ++ toString aFold ++
      " len=" ++ toString aLen ++ " contractScene=" ++ toString aSceneReal ++
      " cRole=" ++ toString aCRole ++ " cRoleT=" ++ toString aRoleT ++
      " mirror=" ++ toString aMirror ++ " fRole=" ++ toString aFRole ++
      " found=" ++ toString aFound ++ " clear=" ++ toString aClear ++
      " fragDisj=" ++ toString aFDisj ++ " sceneAnc=" ++ toString aSAnc ++
      " env=" ++ toString aEnv ++ " envDisj=" ++ toString aEnvDisj

#eval ncrrGeomTBool "state" ncrrState
#eval ncrrGeomTBool "group" ncrrGroup
#eval ncrrGeomTBool "solo" ncrrSolo
#eval ncrrGeomTBool "bareGroup" ncrrBareGroup
#eval ncrrGeomTBool "empty" ncrrEmpty
#eval ncrrGeomTBool "twoNotes" ncrrTwoNotes

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- The remaining `notes_c8a'` premises on one executed input: C8 of the
contracted scene and of every fragment part/note scene (`Validator.c8`
implies `C8a` via `c8_iff`). -/
private def ncrrBaseC8Bool (name : String) (inp : Input) : String :=
  match ncrrPhases inp with
  | .error e => name ++ ": ERROR " ++ toString (repr e)
  | .ok (_, contracted, layouts, _, _) =>
    let cBase := Validator.c8 contracted.scene.layoutDump
    let cPart := layouts.all fun l => Validator.c8 l.part.scene.layoutDump
    let cNote := layouts.all fun l => l.notes.all fun q => Validator.c8 q.2.scene.layoutDump
    name ++ ": contractedC8=" ++ toString cBase ++
      " partC8=" ++ toString cPart ++ " noteC8=" ++ toString cNote

#eval ncrrBaseC8Bool "state" ncrrState
#eval ncrrBaseC8Bool "group" ncrrGroup
#eval ncrrBaseC8Bool "solo" ncrrSolo
#eval ncrrBaseC8Bool "bareGroup" ncrrBareGroup
#eval ncrrBaseC8Bool "empty" ncrrEmpty
#eval ncrrBaseC8Bool "twoNotes" ncrrTwoNotes

end PipelineImpl
end Layered
end Elegant
