import Elegant.Chart.TreemapClearanceFacts
import Elegant.Chart.TreemapContainmentFacts
import Elegant.Chart.TreemapFacts
import Elegant.Kinds.Treemap
import ElegantGeometry.Validator

/-! Clause C8a and the shared laminar-disjointness fact for the treemap
adapter.

The tiling fold places every child tile inside its parent's tile
(`ProcessedContained`), and `squarify` keeps sibling tiles pairwise disjoint
(`SiblingDisjoint`). Walking the two ancestor chains until they diverge at the
children of the lowest common ancestor (or at the virtual root) transports the
sibling disjointness outward: any two boxes whose ids are neither equal nor
ancestor-related carry disjoint rectangles. `treemap_c8a` is clause C8a of the
validator; the public `treemap_tiles_laminar_disjoint` is the same fact stated
over the dump of a successful layout, consumed by the sibling C7/C8b module. -/

namespace Elegant.Treemap.C8a

open Elegant.Treemap.CanvasC1
open Elegant.Treemap.Clearance
open Elegant.Treemap.TileForest
open Elegant.Treemap.Containment

variable {m : Model}

/-! ### Small list helpers -/

/-- Two indices of a nodup list carrying the same element are equal. -/
theorem getElem?_pos_eq {α : Type} {l : List α} (hn : l.Nodup) {i j : Nat}
    {a : α} (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hi
  exact (List.Nodup.getElem?_inj hbound hn).mp (hi.trans hj.symm)

/-- Every index of a node list appears in its `dependencyOrder`. -/
theorem index_mem_dependencyOrder (nodes : List Node) (j : Nat) (n : Node)
    (hj : nodes[j]? = some n) : j ∈ dependencyOrder nodes := by
  have hjb : j < nodes.length := (List.getElem?_eq_some_iff.mp hj).1
  apply (dependencyOrder_perm_indices nodes).mem_iff.mpr
  rw [List.zipIdx_map_snd]
  rw [List.mem_range'_1]
  exact ⟨Nat.zero_le j, by omega⟩

/-- The tiled output of `tileNodes` carries the same sources as its input. -/
theorem tiled_source {c : Consts} {seed final : List Node}
    (h : tileNodes c seed = .ok final) :
    final.map Node.source = seed.map Node.source :=
  tileNodes_source c seed final h

/-- Ancestor-list membership only grows with more fuel. -/
theorem boxAncestors_mem_mono {boxes : List ModelBox} {k : Nat} {id : String}
    {x : String} (hx : x ∈ boxAncestors boxes k id) (n : Nat) :
    x ∈ boxAncestors boxes (k + n) id :=
  (Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_prefix boxes
    (Nat.le_add_right k n) id).mem hx

/-! ### The tiled context of one successful layout -/

/-- Execution context of one successful treemap layout: the seeded and tiled
node lists with their hygiene facts. -/
structure Ctx (m : Model) where
  seed : List Node
  final : List Node
  hwf : WellFormed m
  hfinal : tileNodes (constants m) seed = .ok final
  hsrc : seed.map Node.source = m.boxes
  hne : ∀ b ∈ m.boxes, b.id ≠ ""
  hw : 0 ≤ (constants m).width
  hh : 0 ≤ (constants m).height
  hseedEq : seed = (assignSeries (aggregate (initialNodes m))).map
    (presetNode m (bandOf m))

/-- Build the context for a given successful layout and node list. -/
def Ctx.forLayout (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (h : Kinds.Treemap.layout m = .ok result)
    (nodes : List Node)
    (hnodes : tileNodes (constants m)
      ((assignSeries (aggregate (initialNodes m))).map (presetNode m (bandOf m)))
        = .ok nodes) : Ctx m :=
  ⟨_, nodes, hwf, hnodes, seeded_source m,
    Kinds.Treemap.layout_box_ids_nonempty m result h,
    Kinds.Treemap.layout_width_nonnegative m result h,
    Kinds.Treemap.layout_height_nonnegative m result h, rfl⟩

variable {ctx : Ctx m}
/-- The seed carries distinct source ids. -/
theorem ctx_nodup0 : (ctx.seed.map (fun n => n.source.id)).Nodup :=
  source_ids_nodup m ctx.hwf ctx.seed ctx.hsrc

/-- The fold preserves the seed invariant through the tiling. -/
theorem ctx_seedinv : ∀ n ∈ ctx.seed, n.rect.Ordered ∧
    Rect.Contained (tileRect (canvasTile (constants m) (bandOf m))) (tileRect n.rect) := by
  have hmem : ∀ n ∈ ctx.seed,
      n ∈ (assignSeries (aggregate (initialNodes m))).map (presetNode m (bandOf m)) := by
    intro n hn
    rw [← ctx.hseedEq]
    exact hn
  intro n hn
  exact seeded_invariant m ctx.hw ctx.hh (bandOf_nonneg m) n (hmem n hn)

/-- Sibling tiles stay disjoint through the whole tiling fold. -/
theorem ctx_sibling : SiblingDisjoint ctx.final := by
  have hfold : (dependencyOrder ctx.seed).foldlM (tileStep (constants m)) ctx.seed =
      .ok ctx.final :=
    (tileNodes_eq_foldlM (constants m) ctx.seed).symm.trans ctx.hfinal
  have hseed : SiblingDisjoint ctx.seed := by
    rw [ctx.hseedEq]
    exact seeded_sibling_disjoint m
  exact foldlM_tile_sibling_disjoint (constants m) (bandOf m) _ _ _ (ctx_seedinv)
    hseed hfold

/-- The box with a given id is found in the model boxes. -/
theorem ctx_find_box {ctx : Ctx m} (b : ModelBox) (hb : b ∈ m.boxes) :
    m.boxes.find? (fun x : ModelBox => x.id == b.id) = some b :=
  findBox_eq m.boxes (Model.boxIds_nodup ctx.hwf) hb

/-- The source of a final node is a model box. -/
theorem ctx_src_mem (n : Node) (hn : n ∈ ctx.final) : n.source ∈ m.boxes := by
  have h1 : n.source ∈ ctx.final.map Node.source := List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [tiled_source ctx.hfinal, ctx.hsrc] at h1
  exact h1

/-- A box of the model lifts to a final node carrying it as source. -/
theorem ctx_final_node_of_box (box : ModelBox) (hbox : box ∈ m.boxes) :
    ∃ p : Node, p ∈ ctx.final ∧ p.source = box := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbox
  have hj2 : (ctx.seed.map Node.source)[j]? = some box := by rw [ctx.hsrc]; exact hj
  rw [List.getElem?_map] at hj2
  obtain ⟨n, hn, hsrcn⟩ := Option.map_eq_some_iff.mp hj2
  obtain ⟨o, ho, hsrco⟩ :=
    source_lookup_of_map_eq ctx.final ctx.seed (tiled_source ctx.hfinal).symm j n hn
  exact ⟨o, List.mem_of_getElem? ho, by rw [hsrco]; exact hsrcn⟩

/-- A final index of the tiled list looks up into the seed. -/
theorem ctx_index {j : Nat} {n : Node} (hj : ctx.final[j]? = some n) :
    ∃ o : Node, ctx.seed[j]? = some o ∧ o.source = n.source :=
  source_lookup_of_map_eq ctx.seed ctx.final (tiled_source ctx.hfinal) j n hj

/-- A final index appears in the seed dependency order. -/
theorem ctx_mem_order {j : Nat} {n : Node} (hj : ctx.final[j]? = some n) :
    j ∈ dependencyOrder ctx.seed := by
  obtain ⟨o, ho, _⟩ := ctx_index hj
  exact index_mem_dependencyOrder ctx.seed j o ho

/-- Every nonempty parent id of a final node names another final node. -/
theorem ctx_parent_node (n : Node) (hn : n ∈ ctx.final)
    (hnp : n.source.parent ≠ "") :
    ∃ p : Node, p ∈ ctx.final ∧ p.source.id = n.source.parent := by
  have hsrcmem : n.source ∈ m.boxes := ctx_src_mem (ctx := ctx) n hn
  have hres := Elegant.parent_induction m ctx.hwf
    (fun id => id = "" ∨ ∃ d ∈ m.boxes, d.id = id) (Or.inl rfl)
    (fun bb hbmem _ => Or.inr ⟨bb, hbmem, rfl⟩) n.source hsrcmem
  cases hres with
  | inl hempty => exact absurd hempty hnp
  | inr hres' =>
    obtain ⟨d, hdm, hdid⟩ := hres'
    obtain ⟨p, hp, hpsrc⟩ := ctx_final_node_of_box (ctx := ctx) d hdm
    exact ⟨p, hp, by rw [hpsrc, hdid]⟩

/-- Parent containment on the final list: the parent's tile contains the
child's tile. -/
theorem ctx_proc_parent (c p : Node) (hc : c ∈ ctx.final) (hp : p ∈ ctx.final)
    (hid : p.source.id = c.source.parent) :
    Rect.Contained (tileRect p.rect) (tileRect c.rect) := by
  have hid' : ∀ t ∈ ctx.seed, t.source.id ≠ "" := by
    intro t ht
    exact ctx.hne t.source (by rw [← ctx.hsrc]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
  have hself : ∀ t ∈ ctx.seed, t.source.parent ≠ t.source.id := by
    intro t ht
    have hmem : t.source ∈ m.boxes := by
      rw [← ctx.hsrc]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
    exact modelBox_parent_ne_id ctx.hwf t.source hmem (hid' t ht)
  have hproc := fold_processedContained ctx.hwf ctx.seed ctx.hsrc hid' hself
    ctx.final (ctx_nodup0) (ctx_seedinv) ctx.hfinal
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
  exact hproc k (ctx_mem_order (ctx := ctx) hk) j c hj
    (by rw [← hid]; exact ctx.hne p.source (ctx_src_mem (ctx := ctx) p hp)) p hk hid

/-- `boxAncestors` unfolds one step at a real box with nonempty parent. -/
theorem ctx_anc_succ {ctx : Ctx m} (x : ModelBox) (hx : x ∈ m.boxes)
    (hpx : x.parent ≠ "") (f : Nat) :
    boxAncestors m.boxes (f + 1) x.id = x.parent :: boxAncestors m.boxes f x.parent := by
  rw [Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq m.boxes f x.id,
    ctx_find_box (ctx := ctx) x hx]
  simp [hpx]

/-- The parent of a final node with nonempty parent id lies inside it. -/
theorem child_in_parent (c : Node) (hc : c ∈ ctx.final) (hcp : c.source.parent ≠ "") :
    ∃ p : Node, p ∈ ctx.final ∧ p.source.id = c.source.parent ∧
      Rect.Contained (tileRect p.rect) (tileRect c.rect) := by
  obtain ⟨p, hp, hpid⟩ := ctx_parent_node c hc hcp
  exact ⟨p, hp, hpid, ctx_proc_parent c p hc hp hpid⟩

/-- `diverge_child`: if `p`'s id sits on `b`'s fuel-`f` ancestor chain and is
not `b` itself, then the chain node under `p` is a final node `c` with `p` as
parent, still on the chain, containing `b`. -/
theorem diverge_child (b : Node) (hb : b ∈ ctx.final) :
    ∀ (f : Nat) (p : Node),
      p.source.id ∈ b.source.id :: boxAncestors m.boxes f b.source.id →
      p.source.id ≠ b.source.id →
      ∃ c : Node, c ∈ ctx.final ∧ c.source.parent = p.source.id ∧
        c.source.id ∈ b.source.id :: boxAncestors m.boxes f b.source.id ∧
        Rect.Contained (tileRect c.rect) (tileRect b.rect) := by
  intro f
  induction f generalizing b with
  | zero =>
    intro p hmem hpid
    have hchain0 : boxAncestors m.boxes 0 b.source.id = [] := rfl
    rw [hchain0] at hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact absurd heq hpid
    · exact absurd hmem' (by simp)
  | succ f ih =>
    intro p hmem hpid
    by_cases hbp : b.source.parent = ""
    · have hmemsrc : b.source ∈ m.boxes := ctx_src_mem (ctx := ctx) b hb
      have hchain : boxAncestors m.boxes (f + 1) b.source.id = [] := by
        rw [Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq m.boxes f
          b.source.id, ctx_find_box (ctx := ctx) b.source hmemsrc]
        simp [hbp]
      rw [hchain] at hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · exact absurd heq hpid
      · exact absurd hmem' (by simp)
    · obtain ⟨pb, hpb, hpbid, hpbcont⟩ := child_in_parent (ctx := ctx) b hb hbp
      have hchain : boxAncestors m.boxes (f + 1) b.source.id =
          b.source.parent :: boxAncestors m.boxes f b.source.parent :=
        ctx_anc_succ (ctx := ctx) b.source (ctx_src_mem (ctx := ctx) b hb) hbp f
      rw [hchain] at hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · exact absurd heq hpid
      rcases List.mem_cons.mp hmem' with heq2 | hmem2
      · -- p is b's direct parent: c := b
        exact ⟨b, hb, heq2.symm, List.mem_cons_self, Rect.Contained.refl _⟩
      · rw [← hpbid] at hmem2
        by_cases hpbeq : p.source.id = pb.source.id
        · exact ⟨b, hb, by rw [← hpbid]; exact hpbeq.symm, List.mem_cons_self,
            Rect.Contained.refl _⟩
        · obtain ⟨c, hc, hcpar, hcid, hccont⟩ := ih pb hpb p
            (List.mem_cons_of_mem _ hmem2) hpbeq
          refine ⟨c, hc, hcpar, ?_, ?_⟩
          · rw [hchain, ← hpbid]
            exact List.mem_cons_of_mem _ hcid
          · exact Rect.Contained.trans hccont hpbcont

/-! ### The laminar fact at node level -/

/-- A real box id resolves to its carrying node in a list whose sources are
those boxes. -/
theorem node_find_of_box (nodes : List Node) (boxes : List ModelBox)
    (hboxes : boxes = nodes.map Node.source)
    (hnodup : (nodes.map (fun n : Node => n.source.id)).Nodup)
    (y : ModelBox) (hy : y ∈ boxes) :
    ∃ n : Node, nodes.find? (fun n_1 : Node => n_1.source.id == y.id) = some n ∧
      n.source = y := by
  have hy' : y ∈ nodes.map Node.source := hboxes ▸ hy
  obtain ⟨n, hn, hns⟩ := List.mem_map.mp hy'
  have hlookup := find_source_id_of_mem nodes hnodup n hn
  refine ⟨n, ?_, hns⟩
  rw [← hns]
  exact hlookup

/-- A real box id cannot carry a zero depth profile: at fuel one its parent
depth is one, not zero. -/
theorem depth_one_of_real (nodes : List Node) (boxes : List ModelBox)
    (hboxes : boxes = nodes.map Node.source)
    (hnodup : (nodes.map (fun n : Node => n.source.id)).Nodup)
    (id : String) (hprof : DepthProfile nodes id 0)
    (hid : id ≠ "") (hreal : ∃ b : ModelBox, b ∈ boxes ∧ b.id = id) : False := by
  obtain ⟨y, hy, hyid⟩ := hreal
  obtain ⟨n, hfind, hns⟩ := node_find_of_box nodes boxes hboxes hnodup y hy
  have hfind' : nodes.find? (fun n_1 : Node => n_1.source.id == id) = some n := by
    rw [show ((fun n_1 : Node => n_1.source.id == id) : Node → Bool) =
      (fun n_1 : Node => n_1.source.id == y.id) from by
        funext x_1; simp [hyid]]
    exact hfind
  have h1 := hprof 1
  simp [parentDepth, hfind'] at h1

/-- The tight profile fact: a depth profile of depth `d` for an id whose parent
chain runs through real boxes certifies the chain test at fuel `max d 1`.
The parent-reality premise is exactly what well-formedness gives for box
parents, and it excludes the dangling terminations that would otherwise need
one extra step of fuel. -/
theorem pce_tight (nodes : List Node) (boxes : List ModelBox)
    (hboxes : boxes = nodes.map Node.source)
    (hnodup : (nodes.map (fun n : Node => n.source.id)).Nodup)
    (hbidnodup : (boxes.map (fun b : ModelBox => b.id)).Nodup)
    (hParReal : ∀ b : ModelBox, b ∈ boxes →
      b.parent = "" ∨ ∃ y : ModelBox, y ∈ boxes ∧ y.id = b.parent) :
    ∀ (d : Nat) (id : String), DepthProfile nodes id d →
      (id = "" ∨ ∃ b : ModelBox, b ∈ boxes ∧ b.id = id) →
      parentChainEnds boxes (Nat.max d 1) id = true := by
  intro d
  induction d with
  | zero =>
    intro id hprof hreal
    have hmax : Nat.max 0 1 = 1 := Nat.max_eq_right (show (0 : Nat) ≤ 1 by omega)
    rw [hmax]
    by_cases hid : id = ""
    · rw [hid]; exact parentChainEnds.eq_1 boxes 1
    · rcases hreal with h0 | hreal'
      · exact absurd h0 hid
      · exact (depth_one_of_real nodes boxes hboxes hnodup id hprof hid
          hreal').elim
  | succ d ih =>
    intro id hprof hreal
    have hmax : Nat.max (d + 1) 1 = d + 1 :=
      Nat.max_eq_left (show (1 : Nat) ≤ d + 1 by omega)
    rw [hmax]
    by_cases hid : id = ""
    · rw [hid]; exact parentChainEnds.eq_1 boxes (d + 1)
    · obtain ⟨b, hb, hbid⟩ := hreal.resolve_left hid
      have hbf : boxes.find? (fun x : ModelBox => x.id == id) = some b := by
        rw [show ((fun x : ModelBox => x.id == id) : ModelBox → Bool) =
          (fun x : ModelBox => x.id == b.id) from by
            funext x_1; simp [hbid]]
        exact findBox_eq boxes hbidnodup hb
      -- the profile steps down to the parent
      obtain ⟨n, hfind, hns⟩ :=
        node_find_of_box nodes boxes hboxes hnodup b hb
      have hfind' : nodes.find? (fun n_1 : Node => n_1.source.id == id) = some n := by
        rw [show ((fun n_1 : Node => n_1.source.id == id) : Node → Bool) =
          (fun n_1 : Node => n_1.source.id == b.id) from by
            funext x_1; simp [hbid]]
        exact hfind
      have hstep : ∀ fuel, parentDepth nodes (fuel + 1) id =
          1 + parentDepth nodes fuel n.source.parent := by
        intro fuel
        simp [parentDepth, hfind']
      have hprof' : DepthProfile nodes b.parent d := by
        intro fuel
        have hs := hprof (fuel + 1)
        rw [hstep fuel, hns] at hs
        omega
      simp only [parentChainEnds.eq_3 boxes id d hid, hbf]
      rcases hParReal b hb with hp0 | ⟨y2, hy2b, hy2id⟩
      · rw [hp0]; exact parentChainEnds.eq_1 boxes d
      · by_cases hpb : b.parent = ""
        · rw [hpb]; exact parentChainEnds.eq_1 boxes d
        · by_cases hd0 : d = 0
          · have hprof0 : DepthProfile nodes b.parent 0 := by
              subst hd0
              exact hprof'
            exact (depth_one_of_real nodes boxes hboxes hnodup b.parent hprof0
              hpb ⟨y2, hy2b, hy2id⟩).elim
          · have hres := ih b.parent hprof' (Or.inr ⟨y2, hy2b, hy2id⟩)
            have hmax1 : Nat.max d 1 = d :=
              Nat.max_eq_left (show (1 : Nat) ≤ d by omega)
            rw [hmax1] at hres
            exact hres

/-- `parentChainEnds` unfolds one step at a real box with nonempty id. -/
theorem ctx_pce_succ {ctx : Ctx m} (x : ModelBox) (hx : x ∈ m.boxes)
    (hxid : x.id ≠ "") (f : Nat) :
    Elegant.Treemap.parentChainEnds m.boxes (f + 1) x.id =
      Elegant.Treemap.parentChainEnds m.boxes f x.parent := by
  rw [Elegant.Treemap.parentChainEnds.eq_3 m.boxes x.id f (by simpa using hxid)]
  simp only [ctx_find_box (ctx := ctx) x hx]

/-- The chain test succeeds at fuel `length` for every model box: the box's
parent carries a depth profile bounded by the box count, and the tight profile
lemma certifies the chain at exactly that fuel. The proof never resolves the
parent through a box with the parent's id, so a parent is never required to be
a box on its own beyond what well-formedness already provides. -/
theorem ctx_pce {ctx : Ctx m} (x : ModelBox) (hx : x ∈ m.boxes) :
    Elegant.Treemap.parentChainEnds m.boxes m.boxes.length x.id = true := by
  have hsrc : (initialNodes m).map Node.source = m.boxes := initialNodes_source m
  have hnodup := source_ids_nodup m ctx.hwf (initialNodes m) hsrc
  have hParReal : ∀ b : ModelBox, b ∈ m.boxes →
      b.parent = "" ∨ ∃ y : ModelBox, y ∈ m.boxes ∧ y.id = b.parent := by
    intro b hb
    exact Elegant.parent_induction m ctx.hwf
      (fun id => id = "" ∨ ∃ y : ModelBox, y ∈ m.boxes ∧ y.id = id)
      (Or.inl rfl)
      (fun c hc hcpar => by
        by_cases hid : c.id = ""
        · exact Or.inl hid
        · exact Or.inr ⟨c, hc, rfl⟩)
      b hb
  have hk : m.boxes.length = (m.boxes.length - 1) + 1 :=
    (Nat.sub_add_cancel
      (List.length_pos_of_mem hx : (1 : Nat) ≤ m.boxes.length)).symm
  by_cases hp : x.parent = ""
  · rw [hk, ctx_pce_succ (ctx := ctx) x hx (ctx.hne x hx) (m.boxes.length - 1),
      hp]
    exact Elegant.Treemap.parentChainEnds.eq_1 m.boxes (m.boxes.length - 1)
  · have hlenEq : (initialNodes m).length = m.boxes.length := by
      simpa using congrArg List.length hsrc
    have hlt := CanvasC1.source_parent_depth_lt_length m ctx.hwf
      (initialNodes m) hsrc x hx
    obtain ⟨depth, hprofP⟩ :=
      CanvasC1.source_parent_depthProfile m ctx.hwf (initialNodes m) hsrc x hx
    obtain ⟨y, hy, hyid⟩ := (hParReal x hx).resolve_left hp
    rw [hprofP (initialNodes m).length, hlenEq] at hlt
    have hd1 : 1 ≤ depth := by
      by_cases hc : 1 ≤ depth
      · exact hc
      · exfalso
        have h0 : depth = 0 := by omega
        rw [h0] at hprofP
        exact depth_one_of_real (initialNodes m) m.boxes hsrc.symm hnodup
          x.parent hprofP hp ⟨y, hy, hyid⟩
    have hpce := pce_tight (initialNodes m) m.boxes hsrc.symm hnodup
      (Model.boxIds_nodup ctx.hwf) hParReal depth x.parent hprofP
      (Or.inr ⟨y, hy, hyid⟩)
    have hmax : Nat.max depth 1 = depth :=
      Nat.max_eq_left (show (1 : Nat) ≤ depth by omega)
    rw [hmax] at hpce
    rw [hk, ctx_pce_succ (ctx := ctx) x hx (ctx.hne x hx) (m.boxes.length - 1)]
    exact ClearanceContainment.cfl_parentChainEnds_mono m.boxes depth
      (m.boxes.length - 1) x.parent (by omega) hpce

/-- The laminar fact: two final nodes whose ids are neither equal nor
ancestor-related carry disjoint tiles. The fuels `fA` and `fB` bound each side's
parent chain and the ancestor membership premises use the matching fuel, so
peeling one parent step drops one fuel. -/
theorem laminar :
    ∀ (s fA fB : Nat), fA + fB = s →
      ∀ a b : Node, a ∈ ctx.final → b ∈ ctx.final →
        Elegant.Treemap.parentChainEnds m.boxes fA a.source.id = true →
        Elegant.Treemap.parentChainEnds m.boxes fB b.source.id = true →
        a.source.id ≠ b.source.id →
        a.source.id ∉ boxAncestors m.boxes fB b.source.id →
        b.source.id ∉ boxAncestors m.boxes fA a.source.id →
        Disjoint (tileRect a.rect) (tileRect b.rect) := by
  intro s
  induction s with
  | zero =>
    intro fA fB hsum a b hafin _ hpa _ _ _ _
    have hfA : fA = 0 := by omega
    subst hfA
    have haid : a.source.id ≠ "" := ctx.hne a.source (ctx_src_mem (ctx := ctx) a hafin)
    rw [Elegant.Treemap.parentChainEnds.eq_2 m.boxes a.source.id haid] at hpa
    exact absurd hpa (by simp)
  | succ s ih =>
    intro fA fB hsum a b hafin hbin hpaA hpbB hidab h1 h2
    have haid : a.source.id ≠ "" := ctx.hne a.source (ctx_src_mem (ctx := ctx) a hafin)
    have hbid : b.source.id ≠ "" := ctx.hne b.source (ctx_src_mem (ctx := ctx) b hbin)
    have hmemA : a.source ∈ m.boxes := ctx_src_mem (ctx := ctx) a hafin
    have hmemB : b.source ∈ m.boxes := ctx_src_mem (ctx := ctx) b hbin
    -- a fuel of zero contradicts the chain test at a nonempty id
    have hfApos : 0 < fA := by
      cases hfA0 : fA with
      | zero =>
        rw [hfA0] at hpaA
        rw [Elegant.Treemap.parentChainEnds.eq_2 m.boxes a.source.id haid] at hpaA
        exact absurd hpaA (by simp)
      | succ k => exact Nat.zero_lt_succ k
    have hfBpos : 0 < fB := by
      cases hfB0 : fB with
      | zero =>
        rw [hfB0] at hpbB
        rw [Elegant.Treemap.parentChainEnds.eq_2 m.boxes b.source.id hbid] at hpbB
        exact absurd hpbB (by simp)
      | succ k => exact Nat.zero_lt_succ k
    obtain ⟨fA1, hfA1⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfApos)
    obtain ⟨fB1, hfB1⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfBpos)
    by_cases hap : a.source.parent = ""
    · by_cases hbp : b.source.parent = ""
      · -- both root-level: siblings
        exact ctx_sibling a hafin b hbin hidab (hap.trans hbp.symm)
      · -- peel b's chain: recurse on (a, pb)
        obtain ⟨pb, hpbin, hpbid, hpbcont⟩ := child_in_parent (ctx := ctx) b hbin hbp
        have hpbpce : Elegant.Treemap.parentChainEnds m.boxes fB1 pb.source.id = true := by
          have hsz : Elegant.Treemap.parentChainEnds m.boxes fB b.source.id = true := hpbB
          rw [hfB1] at hsz
          rw [ctx_pce_succ (ctx := ctx) b.source hmemB hbid fB1] at hsz
          rwa [← hpbid] at hsz
        have hAncA : boxAncestors m.boxes fA a.source.id = [] := by
          rw [hfA1, Nat.succ_eq_add_one,
            Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq m.boxes fA1
              a.source.id,
            ctx_find_box (ctx := ctx) a.source hmemA]
          simp [hap]
        have hAncB : boxAncestors m.boxes fB b.source.id =
            b.source.parent :: boxAncestors m.boxes fB1 b.source.parent := by
          rw [hfB1, Nat.succ_eq_add_one]
          exact ctx_anc_succ (ctx := ctx) b.source hmemB hbp fB1
        have h1full : a.source.id ∉ boxAncestors m.boxes fB1 pb.source.id := by
          have h1' : a.source.id ∉
              b.source.parent :: boxAncestors m.boxes fB1 b.source.parent := by
            rw [← hAncB]; exact h1
          rw [hpbid]
          exact fun hm => h1' (List.mem_cons_of_mem _ hm)
        have hpab : a.source.id ≠ pb.source.id := by
          intro hcon
          have h1' : a.source.id ∉
              b.source.parent :: boxAncestors m.boxes fB1 b.source.parent := by
            rw [← hAncB]; exact h1
          exact h1' (List.mem_cons.mpr (Or.inl (hcon.trans hpbid)))
        have hstep := ih fA fB1 (by omega) a pb hafin hpbin hpaA hpbpce hpab h1full
          (by rw [hAncA]; exact List.not_mem_nil)
        -- b lies inside pb
        refine tile_disjoint_symm _ _
          (disjoint_of_contained_disjoint hpbcont (tile_disjoint_symm _ _ hstep))
    · by_cases hbp : b.source.parent = ""
      · -- peel a's chain: recurse on (pa, b)
        obtain ⟨pa, hpain, hpaid, hpacont⟩ := child_in_parent (ctx := ctx) a hafin hap
        have hpapce : Elegant.Treemap.parentChainEnds m.boxes fA1 pa.source.id = true := by
          have hsz : Elegant.Treemap.parentChainEnds m.boxes fA a.source.id = true := hpaA
          rw [hfA1] at hsz
          rw [ctx_pce_succ (ctx := ctx) a.source hmemA haid fA1] at hsz
          rwa [← hpaid] at hsz
        have hAncB : boxAncestors m.boxes fB b.source.id = [] := by
          rw [hfB1, Nat.succ_eq_add_one,
            Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq m.boxes fB1
              b.source.id,
            ctx_find_box (ctx := ctx) b.source hmemB]
          simp [hbp]
        have hAncA : boxAncestors m.boxes fA a.source.id =
            a.source.parent :: boxAncestors m.boxes fA1 a.source.parent := by
          rw [hfA1, Nat.succ_eq_add_one]
          exact ctx_anc_succ (ctx := ctx) a.source hmemA hap fA1
        have hpab : pa.source.id ≠ b.source.id := by
          intro hcon
          have h2' : b.source.id ∉
              a.source.parent :: boxAncestors m.boxes fA1 a.source.parent := by
            rw [← hAncA]; exact h2
          exact h2' (List.mem_cons.mpr (Or.inl (hcon.symm.trans hpaid)))
        have h2full : b.source.id ∉ boxAncestors m.boxes fA1 pa.source.id := by
          have h2' : b.source.id ∉
              a.source.parent :: boxAncestors m.boxes fA1 a.source.parent := by
            rw [← hAncA]; exact h2
          rw [hpaid]
          exact fun hm => h2' (List.mem_cons_of_mem _ hm)
        have hstep := ih fA1 fB (by omega) pa b hpain hbin hpapce hpbB hpab
          (by rw [hAncB]; exact List.not_mem_nil)
          h2full
        -- a lies inside pa
        exact disjoint_of_contained_disjoint hpacont hstep
      · -- both parents exist
        obtain ⟨pa, hpain, hpaid, hpacont⟩ := child_in_parent (ctx := ctx) a hafin hap
        obtain ⟨pb, hpbin, hpbid, hpbcont⟩ := child_in_parent (ctx := ctx) b hbin hbp
        have hpapce : Elegant.Treemap.parentChainEnds m.boxes fA1 pa.source.id = true := by
          have hsz : Elegant.Treemap.parentChainEnds m.boxes fA a.source.id = true := hpaA
          rw [hfA1] at hsz
          rw [ctx_pce_succ (ctx := ctx) a.source hmemA haid fA1] at hsz
          rwa [← hpaid] at hsz
        have hpbpce : Elegant.Treemap.parentChainEnds m.boxes fB1 pb.source.id = true := by
          have hsz : Elegant.Treemap.parentChainEnds m.boxes fB b.source.id = true := hpbB
          rw [hfB1] at hsz
          rw [ctx_pce_succ (ctx := ctx) b.source hmemB hbid fB1] at hsz
          rwa [← hpbid] at hsz
        have hAncA : boxAncestors m.boxes fA a.source.id =
            a.source.parent :: boxAncestors m.boxes fA1 a.source.parent := by
          rw [hfA1, Nat.succ_eq_add_one]
          exact ctx_anc_succ (ctx := ctx) a.source hmemA hap fA1
        have hAncB : boxAncestors m.boxes fB b.source.id =
            b.source.parent :: boxAncestors m.boxes fB1 b.source.parent := by
          rw [hfB1, Nat.succ_eq_add_one]
          exact ctx_anc_succ (ctx := ctx) b.source hmemB hbp fB1
        have h2head : b.source.id ≠ a.source.parent := by
          have h2' : b.source.id ∉
              a.source.parent :: boxAncestors m.boxes fA1 a.source.parent := by
            rw [← hAncA]; exact h2
          exact fun hcon => h2' (List.mem_cons.mpr (Or.inl hcon))
        have h2full : b.source.id ∉ boxAncestors m.boxes fA1 pa.source.id := by
          have h2' : b.source.id ∉
              a.source.parent :: boxAncestors m.boxes fA1 a.source.parent := by
            rw [← hAncA]; exact h2
          rw [hpaid]
          exact fun hm => h2' (List.mem_cons_of_mem _ hm)
        have h1head : a.source.id ≠ b.source.parent := by
          have h1' : a.source.id ∉
              b.source.parent :: boxAncestors m.boxes fB1 b.source.parent := by
            rw [← hAncB]; exact h1
          exact fun hcon => h1' (List.mem_cons.mpr (Or.inl hcon))
        have h1full : a.source.id ∉ boxAncestors m.boxes fB1 pb.source.id := by
          have h1' : a.source.id ∉
              b.source.parent :: boxAncestors m.boxes fB1 b.source.parent := by
            rw [← hAncB]; exact h1
          rw [hpbid]
          exact fun hm => h1' (List.mem_cons_of_mem _ hm)
        have hpab : pa.source.id ≠ b.source.id := by
          intro hcon
          exact h2head (hcon.symm.trans hpaid)
        by_cases hsib : pa.source.id = pb.source.id
        · -- a and b are siblings
          exact ctx_sibling a hafin b hbin hidab
            (by rw [← hpaid, ← hpbid]; exact hsib)
        by_cases hA : pa.source.id ∈
            b.source.id :: boxAncestors m.boxes fB b.source.id
        · -- diverge on b's side at pa
          obtain ⟨c, hc, hcpar, hcid, hccont⟩ :=
            diverge_child b hbin fB pa hA hpab
          have hca : c.source.id ≠ a.source.id := by
            intro hcon
            rw [hcon] at hcid
            rcases List.mem_cons.mp hcid with heq | hmem'
            · exact hidab heq
            · exact h1 hmem'
          have hs : Disjoint (tileRect a.rect) (tileRect c.rect) :=
            ctx_sibling a hafin c hc (fun h => hca h.symm)
              (hpaid.symm.trans hcpar.symm)
          refine tile_disjoint_symm _ _
            (disjoint_of_contained_disjoint hccont (tile_disjoint_symm _ _ hs))
        by_cases hA2 : pb.source.id ∈
            a.source.id :: boxAncestors m.boxes fA a.source.id
        · -- diverge on a's side at pb
          have hpba : pb.source.id ≠ a.source.id := by
            intro hcon
            have h1'' : a.source.id ∉
                b.source.parent :: boxAncestors m.boxes fB1 b.source.parent := by
              rw [← hAncB]; exact h1
            exact h1'' (List.mem_cons.mpr (Or.inl (hcon.symm.trans hpbid)))
          obtain ⟨c, hc, hcpar, hcid, hccont⟩ :=
            diverge_child a hafin fA pb hA2 hpba
          have hcb : c.source.id ≠ b.source.id := by
            intro hcon
            rw [hcon] at hcid
            rcases List.mem_cons.mp hcid with heq | hmem'
            · exact hidab heq.symm
            · exact h2 hmem'
          have hs : Disjoint (tileRect b.rect) (tileRect c.rect) :=
            ctx_sibling b hbin c hc (fun h => hcb h.symm)
              (hpbid.symm.trans hcpar.symm)
          exact disjoint_of_contained_disjoint hccont (tile_disjoint_symm _ _ hs)
        · -- both chains miss the other's parent: recurse on (pa, b)
          have hstep := ih fA1 fB (by omega) pa b hpain hbin hpapce hpbB hpab
            (fun hm => hA (List.mem_cons_of_mem _ hm)) h2full
          exact disjoint_of_contained_disjoint hpacont hstep

/-! ### The dump-level bridge and public theorems -/

/-- The dump's ancestor walk computes the same list as `boxAncestors` over a
box list with matching ids and parents. -/
theorem dump_ancestors_eq (d : LayoutDump) (boxes : List ModelBox)
    (hfind : ∀ b ∈ boxes, boxes.find? (fun x : ModelBox => x.id == b.id) = some b)
    (hf : ∀ c ∈ d.boxes, ∃ b ∈ boxes, b.id = c.id ∧ b.parent = c.parent)
    (hb : ∀ b ∈ boxes, ∃ c ∈ d.boxes, c.id = b.id ∧ c.parent = b.parent) :
    ∀ (fuel : Nat) (s : String),
      LayoutDump.ancestors.go d fuel s = boxAncestors boxes fuel s := by
  intro fuel s
  induction fuel generalizing s with
  | zero => rfl
  | succ f ih =>
    have hgo : LayoutDump.ancestors.go d (f + 1) s =
        match d.box? s with
        | none => []
        | some c => if c.parent = "" then []
                    else c.parent :: LayoutDump.ancestors.go d f c.parent := rfl
    rw [hgo, Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq boxes f s]
    simp only [LayoutDump.box?]
    cases hd : d.boxes.find? (fun b : Box => b.id == s) with
    | none =>
      have hnf : boxes.find? (fun b : ModelBox => b.id == s) = none := by
        cases hbx : boxes.find? (fun b : ModelBox => b.id == s) with
        | none => rfl
        | some bx =>
          exfalso
          have hbxid : bx.id = s := by simpa using List.find?_some hbx
          obtain ⟨c, hcm, hcid, _⟩ := hb bx (List.mem_of_find?_eq_some hbx)
          have hno := List.find?_eq_none.mp hd c hcm
          exact hno (by rw [hcid, hbxid]; simp)
      simp only [hnf]
    | some c =>
      obtain ⟨b, hbm, hbid, hbpar⟩ := hf c (List.mem_of_find?_eq_some hd)
      have hcs : c.id = s := by simpa using List.find?_some hd
      have hbid_s : b.id = s := by rw [hbid, hcs]
      have hbf : boxes.find? (fun x : ModelBox => x.id == s) = some b := by
        rw [show (fun x : ModelBox => x.id == s) =
              (fun x : ModelBox => x.id == b.id) from by
            funext x; simp [hbid_s]]
        exact hfind b hbm
      simp only [hbf, hbpar]
      rw [ih]

/-- The shared laminar-disjointness fact, stated over the dump of a successful
treemap layout: two boxes whose ids are neither equal nor ancestor-related
carry disjoint rectangles. -/
theorem treemap_tiles_laminar_disjoint (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (h : Kinds.Treemap.layout m = .ok result) :
    ∀ a ∈ result.scene.layoutDump.boxes, ∀ b ∈ result.scene.layoutDump.boxes,
      a.id ≠ b.id → a.id ∉ result.scene.layoutDump.ancestors b.id →
        b.id ∉ result.scene.layoutDump.ancestors a.id → Disjoint a.rect b.rect := by
  intro a ha b hbmem hidab h1 h2
  obtain ⟨nodes, hnodes, hboxes, _, _⟩ := layout_execution m result.scene
    (Kinds.Treemap.layout_adapter_success m result h)
  let hctx : Ctx m := Ctx.forLayout m result hwf h nodes hnodes
  have hdBoxes : result.scene.layoutDump.boxes = nodes.map (fun n : Elegant.Treemap.Node =>
      ({ id := n.source.id, role := n.source.role.id, rect := tileRect n.rect,
         parent := n.source.parent, exclusive := n.source.exclusive : Box })) :=
    hboxes
  have hlen : result.scene.layoutDump.boxes.length = m.boxes.length := by
    rw [hdBoxes, List.length_map]
    have h1len : nodes.length =
        ((assignSeries (aggregate (initialNodes m))).map
          (presetNode m (bandOf m))).length := by
      simpa using congrArg List.length (tiled_source hnodes)
    have h2len : ((assignSeries (aggregate (initialNodes m))).map
          (presetNode m (bandOf m))).length = m.boxes.length := by
      simpa using congrArg List.length (seeded_source m)
    omega
  have hfd : ∀ c ∈ result.scene.layoutDump.boxes,
      ∃ bx ∈ m.boxes, bx.id = c.id ∧ bx.parent = c.parent := by
    intro c hc
    rw [hdBoxes] at hc
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hc
    exact ⟨n.source, ctx_src_mem (ctx := hctx) n hn, rfl, rfl⟩
  have hbd : ∀ bx ∈ m.boxes, ∃ c ∈ result.scene.layoutDump.boxes,
      c.id = bx.id ∧ c.parent = bx.parent := by
    intro bx hbx
    obtain ⟨p, hp, hpsrc⟩ := ctx_final_node_of_box (ctx := hctx) bx hbx
    refine ⟨⟨p.source.id, p.source.role.id, tileRect p.rect, p.source.parent,
      p.source.exclusive⟩, ?_, ?_, ?_⟩
    · rw [hdBoxes]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    · rw [hpsrc]
    · rw [hpsrc]
  have hAncB : result.scene.layoutDump.ancestors b.id =
      boxAncestors m.boxes m.boxes.length b.id := by
    rw [show result.scene.layoutDump.ancestors b.id =
        LayoutDump.ancestors.go result.scene.layoutDump
          result.scene.layoutDump.boxes.length b.id from rfl,
      dump_ancestors_eq result.scene.layoutDump m.boxes
        (fun bx hx => ctx_find_box (ctx := hctx) bx hx) hfd hbd, hlen]
  have hAncA : result.scene.layoutDump.ancestors a.id =
      boxAncestors m.boxes m.boxes.length a.id := by
    rw [show result.scene.layoutDump.ancestors a.id =
        LayoutDump.ancestors.go result.scene.layoutDump
          result.scene.layoutDump.boxes.length a.id from rfl,
      dump_ancestors_eq result.scene.layoutDump m.boxes
        (fun bx hx => ctx_find_box (ctx := hctx) bx hx) hfd hbd, hlen]
  rw [hdBoxes] at ha hbmem
  obtain ⟨na, hnMem, hna⟩ := List.mem_map.mp ha
  obtain ⟨nb, hnMemB, hnb⟩ := List.mem_map.mp hbmem
  have hpceA := ctx_pce (ctx := hctx) na.source (ctx_src_mem (ctx := hctx) na hnMem)
  have hpceB := ctx_pce (ctx := hctx) nb.source (ctx_src_mem (ctx := hctx) nb hnMemB)
  have hN : m.boxes.length + m.boxes.length = 2 * m.boxes.length := by omega
  have hAid : a.id = na.source.id := by rw [← hna]
  have hBid : b.id = nb.source.id := by rw [← hnb]
  have hArect : a.rect = tileRect na.rect := by rw [← hna]
  have hBrect : b.rect = tileRect nb.rect := by rw [← hnb]
  have hprem1 : na.source.id ≠ nb.source.id := by
    intro hcon
    rw [← hAid, ← hBid] at hcon
    exact hidab hcon
  have hprem2 : na.source.id ∉ boxAncestors m.boxes m.boxes.length nb.source.id := by
    intro hcon
    refine h1 ?_
    rw [hAncB, hAid, hBid]
    exact hcon
  have hprem3 : nb.source.id ∉ boxAncestors m.boxes m.boxes.length na.source.id := by
    intro hcon
    refine h2 ?_
    rw [hAncA, hBid, hAid]
    exact hcon
  have hres := laminar (ctx := hctx) (2 * m.boxes.length) m.boxes.length
    m.boxes.length hN na nb hnMem hnMemB hpceA hpceB hprem1 hprem2 hprem3
  rwa [hArect, hBrect]

/-- Clause C8a of the validator for the treemap adapter. -/
theorem treemap_c8a (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : Kinds.Treemap.layout m = .ok result) :
    Validator.C8a result.scene.layoutDump := by
  intro g hg _ b hbmem hbid h1 h2
  exact treemap_tiles_laminar_disjoint m result hwf h g hg b hbmem
    (fun hcon => hbid hcon.symm) h1 h2

end Elegant.Treemap.C8a
