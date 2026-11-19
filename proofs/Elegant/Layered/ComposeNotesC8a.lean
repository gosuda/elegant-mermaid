import Elegant.Layered.NoteParents
import Elegant.Layered.NoteFootprintDisjoint
import ElegantGeometry.Validator

set_option autoImplicit false

deriving instance Inhabited for Box

/-! Composition validity for attached-note bundles: from a successful `composeNotes` run,
the ancestor relation of the composed scene is the input model's ancestor relation, and the
composed scene satisfies validator clause C8a whenever the contracted scene does and the
placed fragment geometry is separated. -/

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! ### Generic list helpers -/

private theorem findSome?_exists {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : β), l.findSome? f = some r → ∃ x, x ∈ l ∧ f x = some r := by
  intro l
  induction l with
  | nil => intro r h; exact absurd h (by simp)
  | cons a rest ih =>
    intro r h
    simp only [List.findSome?_cons] at h
    cases hfa : f a with
    | some b =>
      rw [hfa] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨a, List.mem_cons_self, hfa⟩
    | none =>
      rw [hfa] at h
      obtain ⟨x, hx, hfx⟩ := ih r h
      exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

private theorem findSome?_none_all {α β : Type} (f : α → Option β) :
    ∀ (l : List α), l.findSome? f = none → ∀ x ∈ l, f x = none := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a rest ih =>
    intro h x hx
    simp only [List.findSome?_cons] at h
    cases hfa : f a with
    | some b => rw [hfa] at h; simp at h
    | none =>
      rw [hfa] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hfa
      · exact ih h x hx'

private theorem find?_ext_mem {α : Type} (p q : α → Bool) (xs : List α)
    (hag : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.find?_cons, hag a List.mem_cons_self,
      ih (fun b hb => hag b (List.mem_cons_of_mem _ hb))]

private theorem find?_unique {α : Type} (f : α → String) :
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

private theorem bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private def okVal {β : Type} [Inhabited β] (e : Except LayoutError β) : β :=
  match e with
    | .ok b => b
    | .error _ => default

private theorem okVal_of_ok {β : Type} [Inhabited β] {e : Except LayoutError β} {b : β}
    (h : e = .ok b) : okVal e = b := by
  rw [h]; rfl

private theorem mapM_ok_exists {α β : Type} [Inhabited β] (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ∃ g : α → β, (∀ a ∈ xs, f a = .ok (g a)) ∧ ys = xs.map g := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    refine ⟨fun _ => default, fun a ha => by simp at ha, ?_⟩
    simpa [List.mapM_nil, pure, Except.pure] using h
  | cons a as ih =>
    intro ys h
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    obtain ⟨g', hg'mem, hg'eq⟩ := ih bs hbs
    refine ⟨fun x => okVal (f x), ?_, ?_⟩
    · intro x hx
      cases hx with
      | head =>
        show f a = Except.ok (okVal (f a))
        rw [hfb, okVal_of_ok rfl]
      | tail _ hx' =>
        show f x = Except.ok (okVal (f x))
        rw [okVal_of_ok (hg'mem x hx')]
        exact hg'mem x hx'
    · rw [← hys, List.map_cons]
      have hga : okVal (f a) = b := okVal_of_ok hfb
      rw [hga]
      refine congrArg (fun l => b :: l) ?_
      rw [hg'eq]
      exact List.map_congr_left (fun x hx => (okVal_of_ok (hg'mem x hx)).symm)

private theorem mem_zip_elim {α β : Type} {a : α} {b : β} {xs : List α} {ys : List β}
    (h : (a, b) ∈ xs.zip ys) : a ∈ xs ∧ b ∈ ys := by
  induction xs generalizing ys with
  | nil => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with hxy | h
      · cases hxy
        exact ⟨List.mem_cons_self, List.mem_cons_self⟩
      · obtain ⟨hm1, hm2⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hm1, List.mem_cons_of_mem _ hm2⟩

/-! ### Geometry helpers -/

private theorem disjoint_shiftRect (a b : Rect) (dx dy : Int) :
    Disjoint (shiftRect dx dy a) (shiftRect dx dy b) ↔ Disjoint a b := by
  simp only [Disjoint, Rect.meetsInterior, shiftRect]
  constructor <;> intro h <;> omega

private theorem meetsInterior_contained {i o x : Rect} (hc : o.Contained i)
    (h : i.meetsInterior x) : o.meetsInterior x := by
  unfold Rect.Contained Rect.meetsInterior at *
  omega

private theorem Disjoint.inner {x o i : Rect} (hd : Disjoint x o) (hc : o.Contained i) :
    Disjoint x i := by
  unfold Disjoint at hd ⊢
  intro hm
  exact hd ((Rect.meetsInterior_comm o x).mp
    (meetsInterior_contained hc ((Rect.meetsInterior_comm x i).mp hm)))

theorem Placed.rect_scene_box {p : Placed} {id : String} {r : Rect} (h : p.rect id = some r) :
    ∃ sb ∈ p.scene.boxes, sb.id = id ∧ shiftRect p.dx p.dy sb.rect = r := by
  rw [Placed.rect, Option.map_eq_some_iff] at h
  obtain ⟨sb, hsb, hr⟩ := h
  refine ⟨sb, List.mem_of_find?_eq_some hsb, ?_, hr⟩
  have := List.find?_some hsb
  simp only [beq_iff_eq] at this
  exact this

/-! ### Composed boxes -/

/-- The rectangle source used by `composeNotes`: the first placed fragment scene that
contains the id, otherwise the contracted scene box. -/
def outRect (placed : List (List Placed)) (contracted : Scene) (id : String) : Option Rect :=
  match List.findSome? (fun x => x.rect id) placed.flatten with
    | some r => some r
    | none => Option.map (fun x => x.rect)
        (List.find? (fun x => x.id == id) contracted.boxes)

/-- The composed dump box of one input box. -/
def outBox (placed : List (List Placed)) (contracted : Scene) (b : ModelBox) :
    Except LayoutError Box :=
  match outRect placed contracted b.id with
    | some rect => Except.ok
        { id := b.id, role := b.role.id, rect := rect, parent := b.parent, exclusive := b.exclusive }
    | _ => Except.error LayoutError.domain

theorem outBox_ok_fields {placed : List (List Placed)} {contracted : Scene} {b : ModelBox}
    {fb : Box} (hok : outBox placed contracted b = .ok fb) :
    fb.id = b.id ∧ fb.role = b.role.id ∧ fb.parent = b.parent ∧ fb.exclusive = b.exclusive ∧
      outRect placed contracted b.id = some fb.rect := by
  simp only [outBox] at hok
  cases hr0 : outRect placed contracted b.id with
  | none => simp only [hr0] at hok; exact absurd hok (by simp)
  | some r =>
    simp only [hr0, Except.ok.injEq] at hok
    have idc : fb.id = b.id := (congrArg Box.id hok).symm
    have rolec : fb.role = b.role.id := (congrArg Box.role hok).symm
    have rectc : fb.rect = r := (congrArg Box.rect hok).symm
    have parentc : fb.parent = b.parent := (congrArg Box.parent hok).symm
    have exclc : fb.exclusive = b.exclusive := (congrArg Box.exclusive hok).symm
    refine ⟨idc, rolec, parentc, exclc, ?_⟩
    rw [← rectc]

theorem classifyRect {placed : List (List Placed)} {contracted : Scene} {id : String}
    {r : Rect} (h : outRect placed contracted id = some r) :
    (∃ p ∈ placed.flatten, p.rect id = some r) ∨
      ((∀ p ∈ placed.flatten, ∀ q : Rect, p.rect id ≠ some q) ∧
        ∃ cg ∈ contracted.boxes, cg.id = id ∧ cg.rect = r) := by
  unfold outRect at h
  by_cases hf : ∃ p ∈ placed.flatten, p.rect id = some r
  · exact Or.inl hf
  · have hnone : List.findSome? (fun x => x.rect id) placed.flatten = none := by
      cases hs : List.findSome? (fun x => x.rect id) placed.flatten with
      | none => rfl
      | some R =>
        obtain ⟨p, hp, hpR⟩ := findSome?_exists (fun x => x.rect id) placed.flatten R hs
        rw [hs] at h
        have hRr : R = r := Option.some.inj h
        exact (hf ⟨p, hp, by
          rw [hpR]; exact congrArg some hRr⟩).elim
    refine Or.inr ⟨fun p hp q hq => ?_, ?_⟩
    · have hpa := findSome?_none_all (fun x => x.rect id) placed.flatten hnone p hp
      simp [hpa] at hq
    · simp only [hnone] at h
      obtain ⟨cb, hcbf, hcbr⟩ := Option.map_eq_some_iff.mp h
      refine ⟨cb, List.mem_of_find?_eq_some hcbf, ?_, hcbr⟩
      have := List.find?_some hcbf
      simpa only [beq_iff_eq] using this

/-- Box characterization of a successful `composeNotes` run. -/
theorem composeNotes_boxes {P : Params} {inp : Input} {o : Options} {margin : Int}
    {lines : List (List Measure.Line)} {contracted : FamilyResult}
    {layouts : List BundleLayout} {atts : List Attach} {scene : Scene}
    (h : composeNotes P inp o margin lines contracted layouts atts = .ok scene) :
    ∃ placed : List (List Placed),
      layouts.mapM (placedFragments margin contracted.scene) = .ok placed ∧
      ∃ F : ModelBox → Box, (∀ b ∈ inp.boxes, outBox placed contracted.scene b = .ok (F b)) ∧
        scene.layoutDump.boxes = inp.boxes.map F := by
  unfold composeNotes at h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨boxes, hb, h⟩ := bind_ok h
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have hscene := Except.ok.inj h
  refine ⟨placed, hp, ?_⟩
  obtain ⟨Fv, hFmem, hFeq⟩ := mapM_ok_exists (outBox placed contracted.scene) inp.boxes boxes hb
  refine ⟨Fv, hFmem, ?_⟩
  have hbx0 : scene.layoutDump.boxes = boxes := by
    rw [← hscene]
    dsimp only [Scene.layoutDump]
  rw [hbx0, hFeq]

/-! ### Fragment bookkeeping -/

/-- The placed fragment entries of one layout (empty if placement failed). -/
def placedOf' (margin : Int) (contracted : Scene) (l : BundleLayout) : List Placed :=
  match placedFragments margin contracted l with
    | .ok ps => ps
    | .error _ => []

theorem placedOf'_eq {margin : Int} {contracted : Scene} {l : BundleLayout} {ps : List Placed}
    (h : placedFragments margin contracted l = .ok ps) :
    placedOf' margin contracted l = ps := by
  simp only [placedOf', h]

theorem placedOf_mem_flatten {margin : Int} {contracted : Scene}
    {layouts : List BundleLayout} {placed : List (List Placed)} {l : BundleLayout} {p : Placed}
    (hok : layouts.mapM (placedFragments margin contracted) = .ok placed)
    (hlm : l ∈ layouts) (hpm : p ∈ placedOf' margin contracted l) :
    p ∈ placed.flatten := by
  obtain ⟨gp, hgpmem, hgpeq⟩ := mapM_ok_exists (placedFragments margin contracted)
    layouts placed hok
  rw [hgpeq, List.mem_flatten]
  refine ⟨placedOf' margin contracted l, ?_, hpm⟩
  rw [placedOf'_eq (hgpmem l hlm)]
  exact List.mem_map.mpr ⟨l, hlm, rfl⟩

theorem placedFlatten_mem {margin : Int} {contracted : Scene}
    {layouts : List BundleLayout} {placed : List (List Placed)} {p : Placed}
    (hok : layouts.mapM (placedFragments margin contracted) = .ok placed)
    (hmem : p ∈ placed.flatten) :
    ∃ l ∈ layouts, p ∈ placedOf' margin contracted l := by
  obtain ⟨gp, hgpmem, hgpeq⟩ := mapM_ok_exists (placedFragments margin contracted)
    layouts placed hok
  rw [hgpeq, List.mem_flatten] at hmem
  obtain ⟨l, hlm, hpl⟩ := hmem
  obtain ⟨l₀, hmem₀, hgp₀⟩ := List.mem_map.mp hlm
  exact ⟨l₀, hmem₀, by rw [placedOf'_eq (hgpmem l₀ hmem₀), hgp₀]; exact hpl⟩

/-- The fragment ids of one bundle: the top, boxes inside the top, and the note ids. -/
def fragmentIdOf (inp : Input) (l : BundleLayout) (id : String) : Bool :=
  id == l.top.id || Compound.inside inp.boxes l.top.id id ||
    (l.notes.map (·.1.id)).contains id

theorem placedOf_scene {margin : Int} {contracted : Scene} {l : BundleLayout} {p : Placed}
    (hmem : p ∈ placedOf' margin contracted l) :
    p.scene = l.part.scene ∨ ∃ q ∈ l.notes, p.scene = q.2.scene := by
  simp only [placedOf'] at hmem
  unfold placedFragments at hmem
  cases hfind : contracted.boxes.find? (fun b => b.id == l.top.id) with
  | none =>
    rw [hfind] at hmem
    exact absurd (show p ∈ ([] : List Placed) from hmem) (by simp)
  | some envelope =>
    rw [hfind] at hmem
    simp only [pure, Except.pure] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact Or.inl rfl
    · rw [List.mem_map] at hmem'
      obtain ⟨q, hq, hpq⟩ := hmem'
      obtain ⟨hn, _⟩ := mem_zip_elim hq
      exact Or.inr ⟨q.1, hn, (congrArg Placed.scene hpq).symm⟩

/-- The contracted scene envelope of one bundle layout. -/
def envRect (contracted : Scene) (l : BundleLayout) : Rect :=
  match contracted.boxes.find? (fun b => b.id == l.top.id) with
    | some b => b.rect
    | none => ⟨0, 0, 0, 0⟩

/-! ### Ancestor congruence and transfer -/

/-- The dump-shaped projection of the input model's boxes. -/
def modelBoxesToDump (bs : List ModelBox) : List Box :=
  bs.map (fun b => Box.mk b.id b.role.id ⟨0, 0, 0, 0⟩ b.parent b.exclusive)

/-- The dump of the input model's boxes, used as the ancestor reference for the composed
scene. -/
def inpDumpOf (inp : Input) : LayoutDump :=
  ⟨⟨0, 0⟩, modelBoxesToDump inp.boxes, [], []⟩

/-- One-directional id/parent transfer between box lists. -/
def IdParentTransfer (src dst : List Box) : Prop :=
  ∀ (s : String) (db : Box), dst.find? (fun b => b.id == s) = some db →
    ∃ sb, src.find? (fun b => b.id == s) = some sb ∧ sb.id = db.id ∧ sb.parent = db.parent

/-- `IdParentTransfer` from mapped model boxes. -/
def IdParentTransferM (src : List ModelBox) (dst : List Box) : Prop :=
  IdParentTransfer (modelBoxesToDump src) dst

theorem IdParentTransfer.trans {a b c : List Box}
    (h1 : IdParentTransfer a b) (h2 : IdParentTransfer b c) : IdParentTransfer a c := by
  intro s db hdb
  obtain ⟨bb, hbf, hid, hpar⟩ := h2 s db hdb
  obtain ⟨ab, haf, hid', hpar'⟩ := h1 s bb hbf
  exact ⟨ab, haf, by rw [hid', hid], by rw [hpar', hpar]⟩

private theorem go_mirror {src dst : List Box} (ht : IdParentTransfer src dst) :
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

private theorem go_mono {d : LayoutDump} {k k' : Nat} (hle : k ≤ k') {s x : String}
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

private theorem contractOne_length_le (inp : Input) (l : BundleLayout) :
    (contractOne inp l).boxes.length ≤ inp.boxes.length := by
  simp only [contractOne, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

private theorem fold_length_le (inp : Input) (layouts : List BundleLayout) :
    (layouts.foldl contractOne inp).boxes.length ≤ inp.boxes.length := by
  induction layouts generalizing inp with
  | nil => simp
  | cons l rest ih =>
    rw [List.foldl_cons]
    exact Nat.le_trans (ih (contractOne inp l)) (contractOne_length_le inp l)

private theorem ancestors_go_boxes_congr {d₁ d₂ : LayoutDump} (hb : d₁.boxes = d₂.boxes)
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

private theorem ancestors_boxes_congr {d₁ d₂ : LayoutDump} (hb : d₁.boxes = d₂.boxes)
    (s : String) : d₁.ancestors s = d₂.ancestors s := by
  unfold LayoutDump.ancestors
  rw [hb]
  exact ancestors_go_boxes_congr hb d₂.boxes.length s

private theorem ancestors_go_map_congr (xs : List ModelBox) (F G : ModelBox → Box)
    (hid : ∀ b ∈ xs, (F b).id = (G b).id)
    (hpar : ∀ b ∈ xs, (F b).parent = (G b).parent)
    (c₁ c₂ : Size) (r₁ r₂ : List Route) (l₁ l₂ : List Label) :
    ∀ (k : Nat) (s : String),
      LayoutDump.ancestors.go ⟨c₁, xs.map F, r₁, l₁⟩ k s =
        LayoutDump.ancestors.go ⟨c₂, xs.map G, r₂, l₂⟩ k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    have hfindF : (⟨c₁, xs.map F, r₁, l₁⟩ : LayoutDump).box? s =
        Option.map F (xs.find? ((fun b => b.id == s) ∘ F)) := by
      simp only [LayoutDump.box?, List.find?_map]
    have hfindG : (⟨c₂, xs.map G, r₂, l₂⟩ : LayoutDump).box? s =
        Option.map G (xs.find? ((fun b => b.id == s) ∘ G)) := by
      simp only [LayoutDump.box?, List.find?_map]
    simp only [LayoutDump.ancestors.go, hfindF, hfindG]
    rw [find?_ext_mem ((fun b => b.id == s) ∘ F) ((fun b => b.id == s) ∘ G) xs
      (fun a ha => by simp only [Function.comp_apply, hid a ha])]
    cases hx : xs.find? ((fun b => b.id == s) ∘ G) with
    | none => rfl
    | some b =>
      simp only [Option.map_some, ← hpar b (List.mem_of_find?_eq_some hx)]
      simp only [ih]

/-- From a successful `composeNotes` run: the composed scene's ancestor relation equals the
input model's ancestor relation. -/
theorem composeNotes_ancestors_eq {P : Params} {inp : Input} {o : Options} {margin : Int}
    {lines : List (List Measure.Line)} {contracted : FamilyResult}
    {layouts : List BundleLayout} {atts : List Attach} {scene : Scene}
    (h : composeNotes P inp o margin lines contracted layouts atts = .ok scene)
    (s : String) :
    scene.layoutDump.ancestors s = (inpDumpOf inp).ancestors s := by
  obtain ⟨placed, hp, F, hFmem, hFboxes⟩ := composeNotes_boxes h
  refine Eq.trans (ancestors_boxes_congr
    (d₂ := ⟨scene.canvas, inp.boxes.map F, scene.routes,
      scene.labels.map (fun l => l.toLabel)⟩) hFboxes s) ?_
  unfold LayoutDump.ancestors
  dsimp only [inpDumpOf]
  rw [show (inp.boxes.map F).length = (modelBoxesToDump inp.boxes).length from by
    simp only [modelBoxesToDump, List.length_map]]
  exact ancestors_go_map_congr inp.boxes F
    (fun b => Box.mk b.id b.role.id ⟨0, 0, 0, 0⟩ b.parent b.exclusive)
    (fun b hb => (outBox_ok_fields (hFmem b hb)).1)
    (fun b hb => (outBox_ok_fields (hFmem b hb)).2.2.1)
    scene.canvas ⟨0, 0⟩ scene.routes [] (scene.labels.map (fun l => l.toLabel)) []
    (modelBoxesToDump inp.boxes).length s

/-! ### `contractOne` keeps ids and parents -/

theorem contractOne_box_mem (inp : Input) (l : BundleLayout) :
    ∀ x ∈ (contractOne inp l).boxes, ∃ ib ∈ inp.boxes, ib.id = x.id ∧ ib.parent = x.parent := by
  intro x hx
  simp only [contractOne, List.mem_map, List.mem_filter] at hx
  obtain ⟨q, hq, hxq⟩ := hx
  obtain ⟨hz, _⟩ := hq
  obtain ⟨_, hlt, hxeq⟩ := List.mem_zipIdx hz
  have hqmem : q.1 ∈ inp.boxes := by
    have hidx : q.2 - 0 < inp.boxes.length := by omega
    rw [hxeq]
    exact List.getElem_mem hidx
  subst hxq
  split
  · exact ⟨q.1, hqmem, rfl, rfl⟩
  · exact ⟨q.1, hqmem, rfl, rfl⟩

theorem contractOne_transfer (inp : Input) (l : BundleLayout)
    (hnd : (inp.boxes.map (fun b => b.id)).Nodup) :
    IdParentTransfer (modelBoxesToDump inp.boxes)
      (modelBoxesToDump (contractOne inp l).boxes) := by
  intro s cb hcb
  have hcbtrue := List.find?_some hcb
  have hcbid : cb.id = s := beq_iff_eq.mp hcbtrue
  subst hcbid
  obtain ⟨ob, hobmem, hdbe⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hcb)
  have hobid : ob.id = cb.id := congrArg Box.id hdbe
  have hobpar : ob.parent = cb.parent := congrArg Box.parent hdbe
  obtain ⟨ib0, hib0mem, hid0, hpar0⟩ := contractOne_box_mem inp l ob hobmem
  have hfind := find?_unique (fun b => b.id)
    (modelBoxesToDump inp.boxes)
    (by simp only [modelBoxesToDump, List.map_map]; exact hnd)
    (Box.mk ib0.id ib0.role.id ⟨0, 0, 0, 0⟩ ib0.parent ib0.exclusive)
    (List.mem_map.mpr ⟨ib0, hib0mem, rfl⟩) cb.id (hid0.trans hobid)
  exact ⟨Box.mk ib0.id ib0.role.id ⟨0, 0, 0, 0⟩ ib0.parent ib0.exclusive, hfind,
    hid0.trans hobid, hpar0.trans hobpar⟩

/-- Equal images under `f` of two members of a list whose image list is duplicate-free
force the members to be equal. -/
private theorem nodup_map_inj_on {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
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
        · exact nodup_map_inj_on f xs h.2 ha' hb' e

/-! ### The composition theorem -/

/-- Bundle composition preserves validator clause C8a: the composed scene's group frames
are separated from foreign boxes whenever the contracted scene satisfies C8a, the placed
fragment geometry is separated, and the fragment scenes realize the input boxes. The
input id uniqueness and the uniqueness of bundle top ids are part of the producer context. -/
theorem composeNotes_c8a
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
    (hcontractrole : ∀ cg ∈ contracted.scene.boxes,
      ∃ ib, inp.boxes.find? (fun b => b.id == cg.id) = some ib ∧ ib.role.id = cg.role)
    (hfragrole : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∃ ib ∈ inp.boxes, ib.id = sb.id ∧ ib.role.id = sb.role)
    (hfragfound : ∀ l ∈ layouts, ∀ id : String, fragmentIdOf inp l id = true →
      (placedOf' margin contracted.scene l).any
        (fun p => p.scene.boxes.any (fun b => b.id == id)) = true)
    (hclear : ∀ l ∈ layouts, ∀ p ∈ placedOf' margin contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∀ cb ∈ contracted.scene.boxes,
        fragmentIdOf inp l cb.id = false →
        Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect)
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
  have hsubc : ∀ (s x : String), x ∈ contracted.scene.layoutDump.ancestors s →
      x ∈ (inpDumpOf inp).ancestors s := by
    intro s x hx
    rw [ancestors_boxes_congr
      (d₂ := ⟨⟨0, 0⟩, contracted.scene.boxes, [], []⟩)
      (show contracted.scene.layoutDump.boxes = contracted.scene.boxes from rfl) s] at hx
    unfold LayoutDump.ancestors at hx ⊢
    have h3 := go_mirror hcontractscene contracted.scene.boxes.length s x hx
    have h4 := go_mirror hfold contracted.scene.boxes.length s x h3
    have hlen : (inpDumpOf inp).boxes.length = inp.boxes.length :=
      List.length_map _
    rw [hlen]
    exact go_mono hclen h4
  intro g hg grole b hb gidne hg1 hg2
  rw [composeNotes_ancestors_eq h] at hg1 hg2
  -- decompose the two output boxes back to input boxes
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
  -- roles and rect sources
  have hrole_g : (F gi).role = gi.role.id := (outBox_ok_fields (hFmem gi hgimem)).2.1
  have hrole_b : (F bi).role = bi.role.id := (outBox_ok_fields (hFmem bi hbimem)).2.1
  have hrect_g : outRect placed contracted.scene gi.id = some g.rect := by
    rw [← hgif]
    exact (outBox_ok_fields (hFmem gi hgimem)).2.2.2.2
  have hrect_b : outRect placed contracted.scene bi.id = some b.rect := by
    rw [← hbif]
    exact (outBox_ok_fields (hFmem bi hbimem)).2.2.2.2
  have hne2 : gi.id ≠ bi.id := gidne.symm
  -- classify both rect sources
  rcases classifyRect hrect_g with hgfrag | ⟨hnotfG, cg, hcgmem, hcgid, hcgr⟩ <;>
  rcases classifyRect hrect_b with hbfrag | ⟨hnotfB, cb, hcbmem, hcbid, hcbr⟩
  · -- both are placed fragment rects
    obtain ⟨pg, hgpf, sg, hsgm, hsgid, hsgshift⟩ :
        ∃ pg ∈ placed.flatten, ∃ sg ∈ pg.scene.boxes, sg.id = gi.id ∧
          shiftRect pg.dx pg.dy sg.rect = g.rect := by
      obtain ⟨p, hpf, hpR⟩ := hgfrag
      obtain ⟨sg, hsgm, hsgid, hshift⟩ := Placed.rect_scene_box hpR
      exact ⟨p, hpf, sg, hsgm, hsgid, hshift⟩
    obtain ⟨pb, hbpf, sb, hsbm, hsbid, hsbshift⟩ :
        ∃ pb ∈ placed.flatten, ∃ sb ∈ pb.scene.boxes, sb.id = bi.id ∧
          shiftRect pb.dx pb.dy sb.rect = b.rect := by
      obtain ⟨p, hpf, hpR⟩ := hbfrag
      obtain ⟨sb, hsbm, hsbid, hshift⟩ := Placed.rect_scene_box hpR
      exact ⟨p, hpf, sb, hsbm, hsbid, hshift⟩
    obtain ⟨lg, hlgm, hpgp⟩ := placedFlatten_mem hp hgpf
    obtain ⟨lb, hlbm, hpbp⟩ := placedFlatten_mem hp hbpf
    by_cases hlge : lg = lb
    · subst hlge
      by_cases hpp : pg = pb
      · subst hpp
        have hne3 : sg.id ≠ sb.id := by rw [hsgid, hsbid]; exact hne2
        have hsgrole : sg.role = "group" := by
          obtain ⟨ib, hibm, hibid, hibrole⟩ := hfragrole lg hlgm pg hpgp sg hsgm
          have h1u := find?_unique (fun b => b.id) inp.boxes hnd ib hibm gi.id
            (hibid.trans hsgid)
          have h2u := find?_unique (fun b => b.id) inp.boxes hnd gi hgimem gi.id rfl
          have hibig : ib = gi := Option.some.inj ((h2u.symm.trans h1u).symm)
          rw [← hibrole, hibig, ← hrole_g, hgif, grole]
        have hA' : sg.id ∉ pg.scene.layoutDump.ancestors sb.id := by
          intro hm
          exact hg1 (by rw [← hsgid, ← hsbid]; exact hsceneAnc lg hlgm pg hpgp sb.id sg.id hm)
        have hB' : sb.id ∉ pg.scene.layoutDump.ancestors sg.id := by
          intro hm
          exact hg2 (by rw [← hsbid, ← hsgid]; exact hsceneAnc lg hlgm pg hpgp sg.id sb.id hm)
        rw [← hsgshift, ← hsbshift]
        refine (disjoint_shiftRect _ _ _ _).mpr ?_
        rcases placedOf_scene hpgp with hps | ⟨q, hqm, hqs⟩
        · rw [hps] at hsgm hsbm hA' hB'
          exact hsame lg hlgm sg hsgm hsgrole sb hsbm (Ne.symm hne3) hA' hB'
        · rw [hqs] at hsgm hsbm hA' hB'
          exact hnote lg hlgm q hqm sg hsgm hsgrole sb hsbm (Ne.symm hne3) hA' hB'
      · -- distinct placed scenes of one bundle
        have hne3 : sg.id ≠ sb.id := by rw [hsgid, hsbid]; exact hne2
        have hd := hfragdisj lg hlgm pg hpgp pb hpbp sg hsgm sb hsbm hpp hne3
        rw [← hsgshift, ← hsbshift]
        exact hd
    · have htopne : lg.top.id ≠ lb.top.id := fun heq =>
        hlge (nodup_map_inj_on (fun l : BundleLayout => l.top.id) layouts htopndup hlgm hlbm heq)
      -- distinct bundles: fragment rects live in disjoint envelopes
      have hd := henvdisj lg hlgm lb hlbm htopne
      have h1' := henv lg hlgm pg hpgp sg hsgm
      have h2' := henv lb hlbm pb hpbp sb hsbm
      rw [hsgshift] at h1'
      rw [hsbshift] at h2'
      have hd1 : Disjoint (envRect contracted.scene lg) b.rect :=
        Disjoint.inner hd h2'
      have hd2 : Disjoint b.rect (envRect contracted.scene lg) :=
        (Disjoint.comm _ _).mp hd1
      have hd3 : Disjoint b.rect g.rect := Disjoint.inner hd2 h1'
      exact (Disjoint.comm _ _).mp hd3
  · -- g fragment, b contracted rect: clear against the foreign contracted box
    obtain ⟨pg, hgpf, sg, hsgm, hsgid, hsgshift⟩ :
        ∃ pg ∈ placed.flatten, ∃ sg ∈ pg.scene.boxes, sg.id = gi.id ∧
          shiftRect pg.dx pg.dy sg.rect = g.rect := by
      obtain ⟨p, hpf, hpR⟩ := hgfrag
      obtain ⟨sg, hsgm, hsgid, hshift⟩ := Placed.rect_scene_box hpR
      exact ⟨p, hpf, sg, hsgm, hsgid, hshift⟩
    obtain ⟨lg, hlgm, hpgp⟩ := placedFlatten_mem hp hgpf
    have hf : fragmentIdOf inp lg cb.id = false := by
      cases hfb : fragmentIdOf inp lg cb.id with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨p, hpm, hsbany⟩ :=
          List.any_eq_true.mp (hfragfound lg hlgm cb.id hfb)
        have hfnd : p.scene.boxes.find? (fun x => x.id == cb.id) ≠ none := by
          intro hfnd0
          rw [List.find?_eq_none] at hfnd0
          obtain ⟨bx, hbxmem, hbxany⟩ := List.any_eq_true.mp hsbany
          exact absurd hbxany (hfnd0 bx hbxmem)
        have hpR : ∃ q : Rect, p.rect cb.id = some q := by
          simp only [Placed.rect]
          cases hfnd' : p.scene.boxes.find? (fun x => x.id == cb.id) with
          | none => exact absurd hfnd' hfnd
          | some _ => exact ⟨_, rfl⟩
        obtain ⟨q, hq⟩ := hpR
        exact hnotfB p (placedOf_mem_flatten hp hlgm hpm) q (by simpa [hcbid] using hq)
    have hdd := hclear lg hlgm pg hpgp sg hsgm cb hcbmem hf
    rw [← hsgshift, ← hcbr]
    exact hdd
  · -- g contracted rect, b fragment: symmetric to the previous case
    obtain ⟨pb, hbpf, sb, hsbm, hsbid, hsbshift⟩ :
        ∃ pb ∈ placed.flatten, ∃ sb ∈ pb.scene.boxes, sb.id = bi.id ∧
          shiftRect pb.dx pb.dy sb.rect = b.rect := by
      obtain ⟨p, hpf, hpR⟩ := hbfrag
      obtain ⟨sb, hsbm, hsbid, hshift⟩ := Placed.rect_scene_box hpR
      exact ⟨p, hpf, sb, hsbm, hsbid, hshift⟩
    obtain ⟨lb, hlbm, hpbp⟩ := placedFlatten_mem hp hbpf
    have hf : fragmentIdOf inp lb cg.id = false := by
      cases hfb : fragmentIdOf inp lb cg.id with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨p, hpm, hsbany⟩ :=
          List.any_eq_true.mp (hfragfound lb hlbm cg.id hfb)
        have hfnd : p.scene.boxes.find? (fun x => x.id == cg.id) ≠ none := by
          intro hfnd0
          rw [List.find?_eq_none] at hfnd0
          obtain ⟨bx, hbxmem, hbxany⟩ := List.any_eq_true.mp hsbany
          exact absurd hbxany (hfnd0 bx hbxmem)
        have hpR : ∃ q : Rect, p.rect cg.id = some q := by
          simp only [Placed.rect]
          cases hfnd' : p.scene.boxes.find? (fun x => x.id == cg.id) with
          | none => exact absurd hfnd' hfnd
          | some _ => exact ⟨_, rfl⟩
        obtain ⟨q, hq⟩ := hpR
        exact hnotfG p (placedOf_mem_flatten hp hlbm hpm) q (by simpa [hcgid] using hq)
    have hz := hclear lb hlbm pb hpbp sb hsbm cg hcgmem hf
    rw [hsbshift, hcgr] at hz
    exact (Rect.disjoint_comm _ _).mpr hz
  · -- both contracted rects: transport the contracted scene's C8a
    obtain ⟨ibg, hibgf, hibgr⟩ := hcontractrole cg hcgmem
    rw [hcgid] at hibgf
    have hibgig : gi = ibg := Option.some.inj
      (((find?_unique (fun b => b.id) inp.boxes hnd gi hgimem gi.id rfl).symm.trans hibgf))
    have hcgrole : cg.role = "group" := by
      rw [← hibgr, ← hibgig, ← hrole_g, hgif, grole]
    have hneAB : cb.id ≠ cg.id := fun hc0 =>
      gidne (hcbid.symm.trans (hc0.trans hcgid))
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

end PipelineImpl
end Layered
end Elegant
