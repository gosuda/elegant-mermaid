import Elegant.Chart.TreemapC8b

namespace Elegant.Treemap.C8b

open Elegant.Treemap.C8a
open Elegant.Treemap.CanvasC1
open Elegant.Treemap.Clearance
open Elegant.Treemap.TileForest
open Elegant.Treemap.Containment
open Elegant.Treemap.LabelFacts
open Elegant.Treemap.LabelFacts3

variable {m : Model}

/-! ### Kernel: nonnegative tile coordinates -/

/-- Kernel: every final tile has non-negative coordinates or is degenerate.
Every final node stays contained in the canvas tile, whose rectangle starts at
the origin. -/
theorem tileRect_nonneg_or_degenerate' (ctx : Ctx m) (n : Node)
    (hn : n ∈ ctx.final) :
    0 ≤ (tileRect n.rect).x ∧ 0 ≤ (tileRect n.rect).y ∨
      (tileRect n.rect).w ≤ 0 ∨ (tileRect n.rect).h ≤ 0 := by
  have hinv := ctx_seedinv (ctx := ctx)
  have hout := tileNodes_invariant (constants m) (bandOf m) ctx.seed ctx.final
    hinv ctx.hfinal
  have hcont := (hout n hn).2
  rw [tileRect_canvasTile] at hcont
  unfold Rect.Contained at hcont
  dsimp only at hcont
  exact Or.inl ⟨hcont.1, hcont.2.2.1⟩

/-! ### Tile margin arithmetic -/

/-- A `containedSpan` with distinct components did not collapse its span. -/
private theorem containedSpan_lt_imp_le {lo hi pLo pHi : Int}
    (h : (containedSpan lo hi pLo pHi).1 < (containedSpan lo hi pLo pHi).2) :
    lo ≤ hi := by
  refine Classical.byContradiction fun hcon => ?_
  have hlt : hi < lo := by omega
  have hc : collapseSpan lo hi =
      (Int.fdiv (lo + hi) 2, Int.fdiv (lo + hi) 2) := by
    unfold collapseSpan
    simp only [hlt, ite_true]
  unfold containedSpan at h
  rw [hc] at h
  simp only at h
  omega

/-- A nondegenerate `containedSpan` (strict components) is the uncollapsed
clipped span. -/
private theorem containedSpan_eq_of_strict {lo hi pLo pHi : Int}
    (h : (containedSpan lo hi pLo pHi).1 < (containedSpan lo hi pLo pHi).2) :
    containedSpan lo hi pLo pHi =
      (max pLo (min pHi lo), max pLo (min pHi hi)) := by
  have hlo : lo ≤ hi := containedSpan_lt_imp_le h
  have hc : collapseSpan lo hi = (lo, hi) := by
    unfold collapseSpan
    split
    · omega
    · rfl
  unfold containedSpan
  rw [hc]

/-- A zero-width cell insets to a zero-width tile. -/
private theorem inset_zero_width_of_zero_width (cell : Tile) (innerX innerY : Int)
    (heq : cell.x0 = cell.x1) :
    (insetCell cell innerX innerY).x0 = (insetCell cell innerX innerY).x1 := by
  simp only [insetCell, containedSpan, collapseSpan]
  rw [heq]
  split <;> simp_all
  · omega

/-- A zero-height cell insets to a zero-height tile. -/
private theorem inset_zero_height_of_zero_height (cell : Tile) (innerX innerY : Int)
    (heq : cell.y0 = cell.y1) :
    (insetCell cell innerX innerY).y0 = (insetCell cell innerX innerY).y1 := by
  simp only [insetCell, containedSpan, collapseSpan]
  rw [heq]
  split <;> simp_all
  · omega

/-- The margin kernel of clause C8b: a cell drawn by `squarify` inside the free
area of an ordered parent insets either to a tile that lies strictly inside the
parent tile with its top edge at or below the header band bottom, or to a
degenerate tile. -/
theorem insetCell_tile_body (P cell : Tile)
    (padX padY header innerX innerY : Int)
    (hP : P.Ordered) (hcell : cell.Ordered)
    (hin : cell.Inside (childArea P padX padY header innerX innerY))
    (hpadX : 1 ≤ padX) (hpadY : 1 ≤ padY) (hband : 1 ≤ header + padY) :
    ((Rect.StrictInside (tileRect P) (tileRect (insetCell cell innerX innerY)) ∧
        P.y0 + header + padY ≤ (insetCell cell innerX innerY).y0) ∨
      (tileRect (insetCell cell innerX innerY)).w ≤ 0 ∨
      (tileRect (insetCell cell innerX innerY)).h ≤ 0) := by
  obtain ⟨hPx, hPy⟩ := hP
  obtain ⟨hcx, hcy⟩ := hcell
  obtain ⟨hin1, hin2, hin3, hin4⟩ := hin
  by_cases hcdx : cell.x0 = cell.x1
  · refine Or.inr (Or.inl ?_)
    have h := inset_zero_width_of_zero_width cell innerX innerY hcdx
    simp only [tileRect]
    omega
  by_cases hcdy : cell.y0 = cell.y1
  · refine Or.inr (Or.inr ?_)
    have h := inset_zero_height_of_zero_height cell innerX innerY hcdy
    simp only [tileRect]
    omega
  have hcxs : cell.x0 < cell.x1 := by omega
  have hcys : cell.y0 < cell.y1 := by omega
  obtain ⟨hFxle, hFyle⟩ := childArea_ordered P padX padY header innerX innerY
  simp only [childArea] at hin1 hin2 hin3 hin4 hFxle hFyle
  have hFx : (containedSpan (P.x0 + padX - Int.fdiv innerX 2)
      (P.x1 - (padX - Int.fdiv innerX 2)) P.x0 P.x1).1 <
      (containedSpan (P.x0 + padX - Int.fdiv innerX 2)
        (P.x1 - (padX - Int.fdiv innerX 2)) P.x0 P.x1).2 := by omega
  have hFy : (containedSpan (P.y0 + header + padY - Int.fdiv innerY 2)
      (P.y1 - (padY - Int.fdiv innerY 2)) P.y0 P.y1).1 <
      (containedSpan (P.y0 + header + padY - Int.fdiv innerY 2)
        (P.y1 - (padY - Int.fdiv innerY 2)) P.y0 P.y1).2 := by omega
  have hfx := containedSpan_eq_of_strict hFx
  have fx0 : (containedSpan (P.x0 + padX - Int.fdiv innerX 2)
      (P.x1 - (padX - Int.fdiv innerX 2)) P.x0 P.x1).1 =
      max P.x0 (min P.x1 (P.x0 + padX - Int.fdiv innerX 2)) :=
    congrArg Prod.fst hfx
  have fx1 : (containedSpan (P.x0 + padX - Int.fdiv innerX 2)
      (P.x1 - (padX - Int.fdiv innerX 2)) P.x0 P.x1).2 =
      max P.x0 (min P.x1 (P.x1 - (padX - Int.fdiv innerX 2))) :=
    congrArg Prod.snd hfx
  have hfy := containedSpan_eq_of_strict hFy
  have fy0 : (containedSpan (P.y0 + header + padY - Int.fdiv innerY 2)
      (P.y1 - (padY - Int.fdiv innerY 2)) P.y0 P.y1).1 =
      max P.y0 (min P.y1 (P.y0 + header + padY - Int.fdiv innerY 2)) :=
    congrArg Prod.fst hfy
  have fy1 : (containedSpan (P.y0 + header + padY - Int.fdiv innerY 2)
      (P.y1 - (padY - Int.fdiv innerY 2)) P.y0 P.y1).2 =
      max P.y0 (min P.y1 (P.y1 - (padY - Int.fdiv innerY 2))) :=
    congrArg Prod.snd hfy
  by_cases hIdx : (containedSpan (cell.x0 + Int.fdiv innerX 2)
      (cell.x1 - Int.fdiv innerX 2) cell.x0 cell.x1).1 =
      (containedSpan (cell.x0 + Int.fdiv innerX 2)
        (cell.x1 - Int.fdiv innerX 2) cell.x0 cell.x1).2
  · refine Or.inr (Or.inl ?_)
    simp only [tileRect, insetCell]
    omega
  by_cases hIdy : (containedSpan (cell.y0 + Int.fdiv innerY 2)
      (cell.y1 - Int.fdiv innerY 2) cell.y0 cell.y1).1 =
      (containedSpan (cell.y0 + Int.fdiv innerY 2)
        (cell.y1 - Int.fdiv innerY 2) cell.y0 cell.y1).2
  · refine Or.inr (Or.inr ?_)
    simp only [tileRect, insetCell]
    omega
  have hxle := containedSpan_ordered (cell.x0 + Int.fdiv innerX 2)
    (cell.x1 - Int.fdiv innerX 2) cell.x0 cell.x1
  have hyle := containedSpan_ordered (cell.y0 + Int.fdiv innerY 2)
    (cell.y1 - Int.fdiv innerY 2) cell.y0 cell.y1
  have hIxs : (containedSpan (cell.x0 + Int.fdiv innerX 2)
      (cell.x1 - Int.fdiv innerX 2) cell.x0 cell.x1).1 <
      (containedSpan (cell.x0 + Int.fdiv innerX 2)
        (cell.x1 - Int.fdiv innerX 2) cell.x0 cell.x1).2 := by omega
  have hIys : (containedSpan (cell.y0 + Int.fdiv innerY 2)
      (cell.y1 - Int.fdiv innerY 2) cell.y0 cell.y1).1 <
      (containedSpan (cell.y0 + Int.fdiv innerY 2)
        (cell.y1 - Int.fdiv innerY 2) cell.y0 cell.y1).2 := by omega
  have hix := containedSpan_eq_of_strict hIxs
  have ix0 : (containedSpan (cell.x0 + Int.fdiv innerX 2)
      (cell.x1 - Int.fdiv innerX 2) cell.x0 cell.x1).1 =
      max cell.x0 (min cell.x1 (cell.x0 + Int.fdiv innerX 2)) :=
    congrArg Prod.fst hix
  have ix1 : (containedSpan (cell.x0 + Int.fdiv innerX 2)
      (cell.x1 - Int.fdiv innerX 2) cell.x0 cell.x1).2 =
      max cell.x0 (min cell.x1 (cell.x1 - Int.fdiv innerX 2)) :=
    congrArg Prod.snd hix
  have hiy := containedSpan_eq_of_strict hIys
  have iy0 : (containedSpan (cell.y0 + Int.fdiv innerY 2)
      (cell.y1 - Int.fdiv innerY 2) cell.y0 cell.y1).1 =
      max cell.y0 (min cell.y1 (cell.y0 + Int.fdiv innerY 2)) :=
    congrArg Prod.fst hiy
  have iy1 : (containedSpan (cell.y0 + Int.fdiv innerY 2)
      (cell.y1 - Int.fdiv innerY 2) cell.y0 cell.y1).2 =
      max cell.y0 (min cell.y1 (cell.y1 - Int.fdiv innerY 2)) :=
    congrArg Prod.snd hiy
  refine Or.inl ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [tileRect, insetCell]
    omega
  · simp only [tileRect, insetCell]
    omega
  · simp only [tileRect, insetCell]
    omega
  · simp only [tileRect, insetCell]
    omega
  · simp only [insetCell]
    omega

/-- The per-index strict nesting fact with band: whenever index `k` holds the
parent of the node at `bIdx`, the parent tile strictly contains the child tile
and the child's top edge lies at or below the parent's header band bottom,
unless the child tile is degenerate. -/
private def NestIdx (c : Consts) (acc : List Node) (k : Nat) : Prop :=
  ∀ bIdx : Nat, ∀ b : Node, acc[bIdx]? = some b → b.source.parent ≠ "" →
    ∀ old : Node, acc[k]? = some old → old.source.id = b.source.parent →
      (Rect.StrictInside (tileRect old.rect) (tileRect b.rect) ∧
        (tileRect old.rect).y + c.header + c.padY ≤ (tileRect b.rect).y) ∨
      (tileRect b.rect).w ≤ 0 ∨ (tileRect b.rect).h ≤ 0

set_option maxHeartbeats 1600000 in
/-- One `tileStep` extends the strict nesting fact from the processed prefix
`done` to `done ++ [i]`. -/
private theorem tileStep_nest {m : Model} (hwf : WellFormed m) (nodes0 : List Node)
    (hsources0 : nodes0.map Node.source = m.boxes)
    (hid0 : ∀ n ∈ nodes0, n.source.id ≠ "")
    (hself0 : ∀ n ∈ nodes0, n.source.parent ≠ n.source.id)
    {c : Consts} {acc mid : List Node} {i : Nat} {done rest : List Nat}
    (hpadX : 1 ≤ c.padX) (hpadY : 1 ≤ c.padY) (hbandc : 1 ≤ c.header + c.padY)
    (hsources_acc : acc.map Node.source = nodes0.map Node.source)
    (hnodup_acc : (acc.map (fun n => n.source.id)).Nodup)
    (hordered_acc : ∀ n ∈ acc, n.rect.Ordered)
    (hdone : ∀ k ∈ done, NestIdx c acc k)
    (hord_step : done ++ i :: rest = dependencyOrder nodes0)
    (hstep : CanvasC1.tileStep c acc i = .ok mid) :
    ∀ k ∈ done ++ [i], NestIdx c mid k := by
  have hordnodup : (dependencyOrder nodes0).Nodup :=
    CanvasC1.dependencyOrder_index_nodup nodes0
  have hi_pos : (dependencyOrder nodes0)[done.length]? = some i := by
    rw [← hord_step]; simp
  have hi_fresh : i ∉ done := by
    intro hmem
    obtain ⟨pos, hposb, hpose⟩ := List.mem_iff_getElem.mp hmem
    have hpos : done[pos]? = some i :=
      List.getElem?_eq_some_iff.mpr ⟨hposb, hpose⟩
    have hposord : (dependencyOrder nodes0)[pos]? = some i := by
      rw [← hord_step, List.getElem?_append_left hposb, hpos]
    have hEq := Containment.getElem?_pos_eq hordnodup hposord hi_pos
    omega
  have hi_mem : i ∈ dependencyOrder nodes0 := by
    rw [← hord_step]; simp
  obtain ⟨inode, hinode0⟩ := CanvasC1.dependencyOrder_index_source nodes0 i hi_mem
  obtain ⟨accnode, haccnode0, hsrcacc⟩ :=
    CanvasC1.source_lookup_of_map_eq acc nodes0 hsources_acc.symm i inode hinode0
  cases hi_acc : acc[i]? with
  | none =>
    simp only [CanvasC1.tileStep, hi_acc, Except.ok.injEq, pure, Except.pure] at hstep
    subst hstep
    intro k hk bIdx b hb hne old hold heq
    rcases List.mem_append.mp hk with hk | hk
    · exact hdone k hk bIdx b hb hne old hold heq
    · have hkeq : k = i := List.mem_singleton.mp hk
      subst hkeq
      rw [hi_acc] at hold
      exact absurd hold (by simp)
  | some parent =>
    have hsrcparent : parent.source = inode.source := by
      have hEq : accnode = parent := Option.some.inj (haccnode0.symm.trans hi_acc)
      rw [hEq] at hsrcacc
      exact hsrcacc
    by_cases hchildren : (sortedChildren acc parent.source.id).isEmpty = true
    · simp only [CanvasC1.tileStep, hi_acc, hchildren, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hstep
      subst hstep
      intro k hk bIdx b hb hne old hold heq
      rcases List.mem_append.mp hk with hk | hk
      · exact hdone k hk bIdx b hb hne old hold heq
      · have hkeq : k = i := List.mem_singleton.mp hk
        subst hkeq
        rw [hi_acc] at hold
        have holdE : parent = old := Option.some.inj hold
        rw [holdE.symm] at heq ⊢
        have hpar : b.source.parent = parent.source.id := heq.symm
        have hmemIdx : bIdx ∈ sortedChildren acc parent.source.id :=
          CanvasC1.sortedChildren_mem_of_lookup acc parent.source.id bIdx b hb hpar
        rw [List.isEmpty_iff.mp hchildren] at hmemIdx
        exact absurd hmemIdx List.not_mem_nil
    · have hchildren' : (sortedChildren acc parent.source.id).isEmpty = false := by
        cases hv : (sortedChildren acc parent.source.id).isEmpty <;> simp_all
      obtain ⟨cells, capped, hsq, hout, _hdisj⟩ :=
        CanvasC1.tileStep_children_execution c acc mid i parent hi_acc hchildren'
          (hordered_acc parent (List.mem_of_getElem? hi_acc)) hstep
      have hzlen : cells.length = (sortedChildren acc parent.source.id).length := by
        simpa only [List.length_map] using
          squarify_length _ _ _ _ cells capped hsq
      have hbOut : ∀ j, (∀ q ∈ (sortedChildren acc parent.source.id).zip cells,
          q.1 ≠ j) → mid[j]? = acc[j]? := by
        intro j hj
        rw [hout]
        exact CanvasC1.batch_getElem?_outside acc
          ((sortedChildren acc parent.source.id).zip cells) c.innerX c.innerY j hj
      have hdoneFresh : ∀ j ∈ done,
          ∀ q ∈ (sortedChildren acc parent.source.id).zip cells, q.1 ≠ j := by
        intro j hj q hq hq1
        exfalso
        obtain ⟨n0, hn0mem, hn0par⟩ := CanvasC1.sortedChildren_index_source acc
          parent.source.id q.1 (List.of_mem_zip hq).1
        have hjmem : j ∈ dependencyOrder nodes0 := by
          rw [← hord_step]; exact List.mem_append_left _ hj
        obtain ⟨cnode0, hcnode0⟩ :=
          CanvasC1.dependencyOrder_index_source nodes0 j hjmem
        obtain ⟨accnodej, haccnodej0, hsrcj⟩ :=
          CanvasC1.source_lookup_of_map_eq acc nodes0 hsources_acc.symm j cnode0
          hcnode0
        have hq1' : q.1 = j := hq1
        have hn0mem' : acc[j]? = some n0 := by
          rw [← hq1']; exact hn0mem
        have hEqn : n0 = accnodej := Option.some.inj (hn0mem'.symm.trans haccnodej0)
        have hjpar : accnodej.source.parent = parent.source.id := by
          rw [← hEqn]; exact hn0par
        have hjpar0 : cnode0.source.parent = inode.source.id := by
          rw [← hsrcj, ← hsrcparent]
          exact hjpar
        obtain ⟨posj, hposjb, hposje⟩ := List.mem_iff_getElem.mp hj
        have hposj : (dependencyOrder nodes0)[posj]? = some j := by
          rw [← hord_step, List.getElem?_append_left hposjb]
          exact List.getElem?_eq_some_iff.mpr ⟨hposjb, hposje⟩
        have hlt := CanvasC1.dependencyOrder_parent_before_child m hwf nodes0
          hsources0 done.length posj i j inode cnode0 hi_pos hposj hinode0 hcnode0
          hjpar0 (hid0 inode (List.mem_of_getElem? hinode0))
        omega
      have hinot : ∀ q ∈ (sortedChildren acc parent.source.id).zip cells,
          q.1 ≠ i := by
        intro q hq hqi
        obtain ⟨n0, hn0mem, hn0par⟩ := CanvasC1.sortedChildren_index_source acc
          parent.source.id q.1 (List.of_mem_zip hq).1
        have hqi' : q.1 = i := hqi
        have hn0mem' : acc[i]? = some n0 := by
          rw [← hqi']; exact hn0mem
        have hEqn : n0 = parent := Option.some.inj (hn0mem'.symm.trans hi_acc)
        rw [hEqn] at hn0par
        have hfinal : inode.source.parent = inode.source.id := by
          rw [← hsrcparent]
          exact hn0par
        exact hself0 inode (List.mem_of_getElem? hinode0) hfinal
      have hi_mid : mid[i]? = some parent := by
        rw [hbOut i hinot]
        exact hi_acc
      intro k hk bIdx b hb hne old hold heq
      rcases List.mem_append.mp hk with hk | hk
      · have hko : mid[k]? = acc[k]? := hbOut k (hdoneFresh k hk)
        rw [hko] at hold
        by_cases hass : bIdx ∈
            ((sortedChildren acc parent.source.id).zip cells).map Prod.fst
        · exfalso
          obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hass
          cases q with
          | mk j _ =>
            have hqb : j = bIdx := hq1
            have hbmem : bIdx ∈ sortedChildren acc parent.source.id := by
              have h1 := (List.of_mem_zip hq).1
              rwa [hqb] at h1
            obtain ⟨n0, hn0mem, hn0par⟩ := CanvasC1.sortedChildren_index_source acc
              parent.source.id bIdx hbmem
            have hbSrc : b.source = n0.source := by
              have hsrc1 : mid.map Node.source = acc.map Node.source :=
                CanvasC1.tileStep_source c acc mid i hstep
              have h : (mid.map Node.source)[bIdx]? =
                  (acc.map Node.source)[bIdx]? := by rw [hsrc1]
              simp only [List.getElem?_map] at h
              rw [hb, hn0mem] at h
              exact Option.some.inj h
            have hbpar_eq : b.source.parent = parent.source.id := by
              rw [hbSrc]; exact hn0par
            have holdid : old.source.id = parent.source.id := heq.trans hbpar_eq
            have hki : k = i := acc_index_eq_of_id_eq hnodup_acc hold hi_acc holdid
            exact hi_fresh (hki ▸ hk)
        · have hbnOut : mid[bIdx]? = acc[bIdx]? := hbOut bIdx (by
            intro q hq hq1
            exact hass (List.mem_map.mpr ⟨q, hq, hq1⟩))
          rw [hbnOut] at hb
          exact hdone k hk bIdx b hb hne old hold heq
      · have hkeq : k = i := List.mem_singleton.mp hk
        subst hkeq
        rw [hi_mid] at hold
        have holdE : parent = old := Option.some.inj hold
        rw [holdE.symm] at heq ⊢
        by_cases hass : bIdx ∈
            ((sortedChildren acc parent.source.id).zip cells).map Prod.fst
        · obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hass
          cases q with
          | mk j cell =>
            have hqb : j = bIdx := hq1
            rw [hqb] at hq
            have hbmem : bIdx ∈ sortedChildren acc parent.source.id :=
              (List.of_mem_zip hq).1
            have hassignNodup : (((sortedChildren acc parent.source.id).zip
                cells).map Prod.fst).Nodup :=
              CanvasC1.zip_indices_nodup (sortedChildren acc parent.source.id) cells
                (CanvasC1.sortedChildren_index_nodup acc parent.source.id)
            obtain ⟨n0, hn0mem, _⟩ := CanvasC1.sortedChildren_index_source acc
              parent.source.id bIdx hbmem
            have hbrect : (mid[bIdx]?).map Node.rect =
                some (insetCell cell c.innerX c.innerY) := by
              rw [hout]
              exact CanvasC1.batch_getElem?_assigned acc
                ((sortedChildren acc parent.source.id).zip cells) c.innerX
                c.innerY hassignNodup (bIdx, cell) hq n0 hn0mem
            rw [hb] at hbrect
            simp only [Option.map_some] at hbrect
            have hbreq : b.rect = insetCell cell c.innerX c.innerY :=
              Option.some.inj hbrect
            rw [hbreq]
            have hvals : ∀ v ∈ (sortedChildren acc parent.source.id).map
                (fun j => (acc[j]?).map (·.value) |>.getD 0), 0 ≤ v :=
              squarify_values_nonnegative _
                (childArea parent.rect c.padX c.padY c.header c.innerX c.innerY)
                c.rho c.fuel cells capped hsq
            have hfree : (childArea parent.rect c.padX c.padY c.header c.innerX
                c.innerY).Ordered :=
              childArea_ordered parent.rect c.padX c.padY c.header c.innerX c.innerY
            have hgeo := squarify_geometry
              ((sortedChildren acc parent.source.id).map
                (fun j => (acc[j]?).map (·.value) |>.getD 0))
              (childArea parent.rect c.padX c.padY c.header c.innerX c.innerY)
              c.rho c.fuel cells capped hvals hfree hsq
            have hcell := hgeo.1 cell (List.of_mem_zip hq).2
            exact insetCell_tile_body parent.rect cell c.padX c.padY c.header
              c.innerX c.innerY
              (hordered_acc parent (List.mem_of_getElem? hi_acc))
              hcell.1 hcell.2 hpadX hpadY hbandc
        · have hbFresh : ∀ q ∈ (sortedChildren acc parent.source.id).zip cells,
              q.1 ≠ bIdx := by
            intro q hq hq1
            exact hass (List.mem_map.mpr ⟨q, hq, hq1⟩)
          have hbnOut : mid[bIdx]? = acc[bIdx]? := hbOut bIdx hbFresh
          rw [hbnOut] at hb
          have hpar : b.source.parent = parent.source.id := heq.symm
          have hmemIdx : bIdx ∈ sortedChildren acc parent.source.id :=
            CanvasC1.sortedChildren_mem_of_lookup acc parent.source.id bIdx b hb hpar
          exfalso
          obtain ⟨pos, hposlt, hpose⟩ := List.mem_iff_getElem.mp hmemIdx
          have hposclt : pos < cells.length := by omega
          have hzipmem : (bIdx, cells[pos]'hposclt) ∈
              (sortedChildren acc parent.source.id).zip cells := by
            rw [List.mem_iff_getElem?]
            refine ⟨pos, ?_⟩
            rw [List.getElem?_zip_eq_some]
            exact ⟨List.getElem?_eq_some_iff.mpr ⟨hposlt, hpose⟩,
              List.getElem?_eq_some_iff.mpr ⟨hposclt, rfl⟩⟩
          exact hbFresh _ hzipmem rfl
/-- The tile fold extends the strict nesting fact to every processed index. -/
private theorem fold_nest {m : Model} (hwf : WellFormed m)
    (nodes0 : List Node) (hsources0 : nodes0.map Node.source = m.boxes)
    (hid0 : ∀ n ∈ nodes0, n.source.id ≠ "")
    (hself0 : ∀ n ∈ nodes0, n.source.parent ≠ n.source.id)
    {c : Consts} {band : Int} (out : List Node)
    (hpadX : 1 ≤ c.padX) (hpadY : 1 ≤ c.padY) (hbandc : 1 ≤ c.header + c.padY)
    (hnodup0 : (nodes0.map (fun n => n.source.id)).Nodup)
    (hseed_inv : ∀ n ∈ nodes0, n.rect.Ordered ∧
      Rect.Contained (tileRect (CanvasC1.canvasTile c band)) (tileRect n.rect))
    (h : tileNodes c nodes0 = .ok out) :
    ∀ k ∈ dependencyOrder nodes0, NestIdx c out k := by
  rw [CanvasC1.tileNodes_eq_foldlM] at h
  have gen : ∀ (l : List Nat) (acc : List Node) (done : List Nat) (out : List Node),
      done ++ l = dependencyOrder nodes0 →
      acc.map Node.source = nodes0.map Node.source →
      (acc.map (fun n => n.source.id)).Nodup →
      (∀ n ∈ acc, n.rect.Ordered ∧
        Rect.Contained (tileRect (CanvasC1.canvasTile c band)) (tileRect n.rect)) →
      (∀ k ∈ done, NestIdx c acc k) →
      l.foldlM (CanvasC1.tileStep c) acc = .ok out →
      ∀ k ∈ done ++ l, NestIdx c out k := by
    intro l
    induction l with
    | nil =>
      intro acc done out hord _ _ _ hdone hfold
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hfold
      subst hfold
      simpa using hdone
    | cons j js ih =>
      intro acc done out hord hsrc hnod hinv hdone hfold
      simp only [List.foldlM] at hfold
      obtain ⟨mid, hmid, hrest⟩ := CanvasC1.except_bind_ok hfold
      have htsrc : mid.map Node.source = nodes0.map Node.source := by
        rw [CanvasC1.tileStep_source c acc mid j hmid, hsrc]
      have htnod : (mid.map (fun n => n.source.id)).Nodup := by
        have hA : mid.map (fun n => n.source.id) =
            List.map (fun x => x.id) (List.map Node.source mid) := by
          rw [List.map_map]
          rfl
        have hB : nodes0.map (fun n => n.source.id) =
            List.map (fun x => x.id) (List.map Node.source nodes0) := by
          rw [List.map_map]
          rfl
        rw [hA, congrArg (fun (l : List ModelBox) => l.map (·.id)) htsrc, ← hB]
        exact hnodup0
      have hstep := tileStep_nest hwf nodes0 hsources0 hid0 hself0 hpadX hpadY hbandc
        hsrc hnod (fun n hn => (hinv n hn).1) hdone hord hmid
      have hinvmid := CanvasC1.tileStep_invariant c band acc j mid hinv hmid
      have hres := ih mid (done ++ [j]) out
        (by rw [List.append_assoc]; exact hord)
        htsrc htnod hinvmid hstep hrest
      simpa only [List.append_assoc, List.singleton_append] using hres
  have h0 := gen (dependencyOrder nodes0) nodes0 [] out rfl rfl hnodup0 hseed_inv
    (fun k hk => absurd hk List.not_mem_nil) h
  simpa using h0

/-- The executed tiling satisfies the strict nesting fact at every final
index. -/
private theorem ctx_nest (ctx : Ctx m) :
    ∀ k ∈ dependencyOrder ctx.seed, NestIdx (constants m) ctx.final k := by
  have hnonempty : ∀ t ∈ ctx.seed, t.source.id ≠ "" := by
    intro t ht
    have hmem : t.source ∈ m.boxes := by
      have h1 : t.source ∈ ctx.seed.map Node.source := List.mem_map.mpr ⟨t, ht, rfl⟩
      rwa [ctx.hsrc] at h1
    exact ctx.hne t.source hmem
  exact fold_nest ctx.hwf ctx.seed ctx.hsrc hnonempty
    (nodes_parent_ne_id ctx.hwf ctx.seed ctx.hsrc ctx_nodup0 hnonempty)
    ctx.final (treemap_padX_ge m) (treemap_padY_ge m) (treemap_band_ge m)
    ctx_nodup0 (ctx_seedinv (ctx := ctx)) ctx.hfinal

/-- The final node list carries distinct source ids. -/
private theorem ctx_final_ids_nodup (ctx : Ctx m) :
    (ctx.final.map (fun n => n.source.id)).Nodup := by
  have h1 : ctx.final.map Node.source = m.boxes := by
    rw [tiled_source ctx.hfinal, ctx.hsrc]
  have h2 : ctx.final.map (fun n => n.source.id) = m.boxes.map (fun b => b.id) := by
    have h := congrArg (fun l : List ModelBox => l.map (fun b => b.id)) h1
    rw [List.map_map] at h
    exact h
  rw [h2]
  exact Model.boxIds_nodup ctx.hwf

/-- Two final nodes with the same source id are equal. -/
private theorem ctx_final_eq_of_id (ctx : Ctx m) {p a : Node}
    (hp : p ∈ ctx.final) (ha : a ∈ ctx.final)
    (hid : p.source.id = a.source.id) : p = a := by
  obtain ⟨pIdx, hpIdx⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨aIdx, haIdx⟩ := List.mem_iff_getElem?.mp ha
  have hp' : (ctx.final.map (fun n => n.source.id))[pIdx]? = some a.source.id := by
    rw [List.getElem?_map, hpIdx]
    exact congrArg some hid
  have ha' : (ctx.final.map (fun n => n.source.id))[aIdx]? = some a.source.id := by
    rw [List.getElem?_map, haIdx]
    rfl
  have hidx := Containment.getElem?_pos_eq (ctx_final_ids_nodup ctx) hp' ha'
  have hlook : ctx.final[pIdx]? = ctx.final[aIdx]? := by rw [hidx]
  rw [hpIdx] at hlook
  exact Option.some.inj (hlook.trans haIdx)

/-- Proper descendants are strictly inside their ancestor with the ancestor's
band below the ancestor's tile top, or degenerate; transported along the
parent chain with fuel bounded by the box count. -/
private theorem tile_chain_strict (ctx : Ctx m) (a : Node) (ha : a ∈ ctx.final) :
    ∀ (k : Nat) (g : Node), g ∈ ctx.final → k ≤ m.boxes.length →
      a.source.id ∈ boxAncestors m.boxes k g.source.id → a.source.id ≠ g.source.id →
      (Rect.StrictInside (tileRect a.rect) (tileRect g.rect) ∧
        (tileRect a.rect).y + (constants m).header + (constants m).padY ≤
          (tileRect g.rect).y) ∨
      (tileRect g.rect).w ≤ 0 ∨ (tileRect g.rect).h ≤ 0 := by
  intro k
  induction k with
  | zero =>
    intro g _ _ hmem _
    have h0 : boxAncestors m.boxes 0 g.source.id = [] := rfl
    rw [h0] at hmem
    exact absurd hmem (by simp)
  | succ k ih =>
    intro g hg hklen hmem hne
    rw [Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_succ_eq
      m.boxes k g.source.id] at hmem
    have hsrcmem : g.source ∈ m.boxes := ctx_src_mem (ctx := ctx) g hg
    have hfind := ctx_find_box (ctx := ctx) g.source hsrcmem
    simp only [hfind] at hmem
    split at hmem
    · exact absurd hmem (by simp)
    · rename_i hpar
      obtain ⟨p, hpmem, hpid⟩ := ctx_parent_node (ctx := ctx) g hg hpar
      have hpg : (Rect.StrictInside (tileRect p.rect) (tileRect g.rect) ∧
          (tileRect p.rect).y + (constants m).header + (constants m).padY ≤
            (tileRect g.rect).y) ∨
          (tileRect g.rect).w ≤ 0 ∨ (tileRect g.rect).h ≤ 0 := by
        obtain ⟨pIdx, hpIdx⟩ := List.mem_iff_getElem?.mp hpmem
        obtain ⟨gIdx, hgIdx⟩ := List.mem_iff_getElem?.mp hg
        exact ctx_nest ctx pIdx (ctx_mem_order (ctx := ctx) hpIdx) gIdx g hgIdx hpar
          p hpIdx (by rw [hpid])
      rcases List.mem_cons.mp hmem with hdirect | hdeep
      · have hpa : p = a := ctx_final_eq_of_id ctx hpmem ha (hpid.trans hdirect.symm)
        subst hpa
        exact hpg
      · have hdeep' : a.source.id ∈ boxAncestors m.boxes k p.source.id := by
          rw [hpid]; exact hdeep
        have hnea : a.source.id ≠ p.source.id := by
          intro heq
          rw [heq] at hdeep'
          have hmono : p.source.id ∈ boxAncestors m.boxes m.boxes.length p.source.id :=
            Elegant.Treemap.Clearance.TileForestHelpers.boxAncestors_prefix
              m.boxes (by omega : k ≤ m.boxes.length) p.source.id |>.mem hdeep'
          exact boxAncestors_irrefl m ctx.hwf p.source.id hmono
        rcases ih p hpmem (by omega) hdeep' hnea with ⟨hsAP, hbAP⟩ | hw | hh
        · rcases hpg with ⟨hsPG, hbPG⟩ | hw' | hh'
          · refine Or.inl ⟨strictInside_trans hsAP hsPG, ?_⟩
            have hB := treemap_band_ge m
            omega
          · exact Or.inr (Or.inl hw')
          · exact Or.inr (Or.inr hh')
        · rcases hpg with ⟨hsPG, _⟩ | hw' | hh'
          · unfold Rect.StrictInside at hsPG
            exact Or.inr (Or.inl (by omega))
          · exact Or.inr (Or.inl hw')
          · exact Or.inr (Or.inr hh')
        · rcases hpg with ⟨hsPG, _⟩ | hw' | hh'
          · unfold Rect.StrictInside at hsPG
            exact Or.inr (Or.inr (by omega))
          · exact Or.inr (Or.inl hw')
          · exact Or.inr (Or.inr hh')

/-- Kernel: proper descendants are strictly inside their ancestors, or
degenerate. -/
theorem tile_strictInside_ancestor' (ctx : Ctx m) (a b : Node)
    (ha : a ∈ ctx.final) (hb : b ∈ ctx.final)
    (hdesc : a.source.id ∈ boxAncestors m.boxes m.boxes.length b.source.id)
    (hne : a.source.id ≠ b.source.id) :
    Rect.StrictInside (tileRect a.rect) (tileRect b.rect) ∨
      (tileRect b.rect).w ≤ 0 ∨ (tileRect b.rect).h ≤ 0 := by
  rcases tile_chain_strict ctx a ha m.boxes.length b hb (Nat.le_refl _) hdesc hne with
    ⟨hs, _⟩ | hw | hh
  · exact Or.inl hs
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr hh)

/-- Kernel: a header-band label of an internal node is vertically clear of
every proper descendant tile. -/
theorem descendant_tile_clear_of_header_label' (ctx : Ctx m) (n g : Node)
    (l : Rect) (hn : n ∈ ctx.final) (hg : g ∈ ctx.final)
    (hdesc : n.source.id ∈ boxAncestors m.boxes m.boxes.length g.source.id)
    (hne : n.source.id ≠ g.source.id)
    (hband : l.y + l.h ≤ (tileRect n.rect).y + (constants m).header + (constants m).padY)
    (_hinside : Rect.StrictInside (tileRect n.rect) l) :
    Disjoint (tileRect g.rect) l := by
  rcases tile_chain_strict ctx n hn m.boxes.length g hg (Nat.le_refl _) hdesc hne with
    ⟨_, hclear⟩ | hw | hh
  · unfold Disjoint Rect.meetsInterior
    intro hm
    have hy := hm.2
    omega
  · exact disjoint_of_degenerate _ _ (Or.inl hw)
  · exact disjoint_of_degenerate _ _ (Or.inr hh)
/-- The band property of one node: its tile starts at or below the reserved
title band, or it is degenerate. -/
private def BandProp (band : Int) (n : Node) : Prop :=
  band ≤ (tileRect n.rect).y ∨ (tileRect n.rect).w ≤ 0 ∨ (tileRect n.rect).h ≤ 0

/-- Clipping into a degenerate span collapses to the single point. -/
private theorem containedSpan_self_fst (lo hi c : Int) :
    (containedSpan lo hi c c).1 = c := by
  unfold containedSpan collapseSpan
  split <;> simp only <;> omega

private theorem containedSpan_self_snd (lo hi c : Int) :
    (containedSpan lo hi c c).2 = c := by
  unfold containedSpan collapseSpan
  split <;> simp only <;> omega

/-- A zero-width parent gives every child cell zero width. -/
private theorem inset_zero_width_of_parent_zero_width (P cell : Tile)
    (padX padY header innerX innerY : Int) (hP0 : P.x0 = P.x1)
    (hcell : cell.Ordered)
    (hin : cell.Inside (childArea P padX padY header innerX innerY)) :
    (insetCell cell innerX innerY).x0 = (insetCell cell innerX innerY).x1 := by
  obtain ⟨hin1, hin2, _, _⟩ := hin
  obtain ⟨hcx, _⟩ := hcell
  simp only [childArea] at hin1 hin2
  rw [hP0] at hin1 hin2
  rw [containedSpan_self_fst] at hin1
  rw [containedSpan_self_snd] at hin2
  exact inset_zero_width_of_zero_width cell innerX innerY (by omega)

/-- A zero-height parent gives every child cell zero height. -/
private theorem inset_zero_height_of_parent_zero_height (P cell : Tile)
    (padX padY header innerX innerY : Int) (hP0 : P.y0 = P.y1)
    (hcell : cell.Ordered)
    (hin : cell.Inside (childArea P padX padY header innerX innerY)) :
    (insetCell cell innerX innerY).y0 = (insetCell cell innerX innerY).y1 := by
  obtain ⟨_, _, hin3, hin4⟩ := hin
  obtain ⟨_, hcy⟩ := hcell
  simp only [childArea] at hin3 hin4
  rw [hP0] at hin3 hin4
  rw [containedSpan_self_fst] at hin3
  rw [containedSpan_self_snd] at hin4
  exact inset_zero_height_of_zero_height cell innerX innerY (by omega)

set_option maxHeartbeats 1600000 in
/-- One tiling step preserves the band property: assigned children sit below
their parent's header band or are degenerate. -/
private theorem tileStep_band (c : Consts) (band : Int) (acc : List Node) (i : Nat)
    (mid : List Node) (hpadX : 1 ≤ c.padX) (hpadY : 1 ≤ c.padY)
    (hbandc : 1 ≤ c.header + c.padY)
    (hinv : ∀ n ∈ acc, n.rect.Ordered ∧
      Rect.Contained (tileRect (CanvasC1.canvasTile c band)) (tileRect n.rect))
    (hband : ∀ n ∈ acc, BandProp band n)
    (h : CanvasC1.tileStep c acc i = .ok mid) :
    ∀ n ∈ mid, BandProp band n := by
  unfold CanvasC1.tileStep at h
  by_cases hi : acc[i]? = none
  · rw [hi] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hband
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp hi
    simp only [hn] at h
    by_cases ho : (sortedChildren acc n.source.id).isEmpty = true
    · rw [ho] at h
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hband
    · have ho' : (sortedChildren acc n.source.id).isEmpty = false := by
        cases hv : (sortedChildren acc n.source.id).isEmpty <;> simp_all
      rw [ho'] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨cells, capped⟩, hsq, hrest⟩ := CanvasC1.except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hrest
      rw [← hrest]
      have hnmem : n ∈ acc := List.mem_of_getElem? hn
      have hPord : n.rect.Ordered := (hinv n hnmem).1
      have hfree : (childArea n.rect c.padX c.padY c.header c.innerX c.innerY).Ordered :=
        childArea_ordered n.rect c.padX c.padY c.header c.innerX c.innerY
      have hnonneg : ∀ v ∈ (sortedChildren acc n.source.id).map
          (fun j => (acc[j]?).map (·.value) |>.getD 0), 0 ≤ v :=
        squarify_values_nonnegative _
          (childArea n.rect c.padX c.padY c.header c.innerX c.innerY)
          c.rho c.fuel cells capped hsq
      have hgeo := squarify_geometry
        ((sortedChildren acc n.source.id).map
          (fun j => (acc[j]?).map (·.value) |>.getD 0))
        (childArea n.rect c.padX c.padY c.header c.innerX c.innerY)
        c.rho c.fuel cells capped hnonneg hfree hsq
      apply CanvasC1.batch_preserves acc
        ((sortedChildren acc n.source.id).zip cells)
        (fun m => BandProp band m) c.innerX c.innerY hband
      intro p hp old _
      obtain ⟨_, hcellmem⟩ := List.of_mem_zip hp
      have hcell := hgeo.1 p.2 hcellmem
      rcases hband n hnmem with hbandn | hwn | hhn
      · have hbody := insetCell_tile_body n.rect p.2 c.padX c.padY c.header
          c.innerX c.innerY hPord hcell.1 hcell.2 hpadX hpadY hbandc
        rcases hbody with ⟨_, hby⟩ | hw | hh
        · refine Or.inl ?_
          have hbn : band ≤ n.rect.y0 := hbandn
          show band ≤ (insetCell p.2 c.innerX c.innerY).y0
          omega
        · exact Or.inr (Or.inl hw)
        · exact Or.inr (Or.inr hh)
      · have hwn' : n.rect.x1 - n.rect.x0 ≤ 0 := hwn
        have hzero : n.rect.x0 = n.rect.x1 := by
          have hox : n.rect.x0 ≤ n.rect.x1 := hPord.1
          omega
        have hw' := inset_zero_width_of_parent_zero_width n.rect p.2 c.padX c.padY
          c.header c.innerX c.innerY hzero hcell.1 hcell.2
        refine Or.inr (Or.inl ?_)
        show (insetCell p.2 c.innerX c.innerY).x1 -
          (insetCell p.2 c.innerX c.innerY).x0 ≤ 0
        omega
      · have hhn' : n.rect.y1 - n.rect.y0 ≤ 0 := hhn
        have hzero : n.rect.y0 = n.rect.y1 := by
          have hoy : n.rect.y0 ≤ n.rect.y1 := hPord.2
          omega
        have hh' := inset_zero_height_of_parent_zero_height n.rect p.2 c.padX c.padY
          c.header c.innerX c.innerY hzero hcell.1 hcell.2
        refine Or.inr (Or.inr ?_)
        show (insetCell p.2 c.innerX c.innerY).y1 -
          (insetCell p.2 c.innerX c.innerY).y0 ≤ 0
        omega

/-- The tile fold preserves the band property through the whole order. -/
private theorem fold_band (c : Consts) (band : Int) (nodes0 out : List Node)
    (hpadX : 1 ≤ c.padX) (hpadY : 1 ≤ c.padY) (hbandc : 1 ≤ c.header + c.padY)
    (hinv0 : ∀ n ∈ nodes0, n.rect.Ordered ∧
      Rect.Contained (tileRect (CanvasC1.canvasTile c band)) (tileRect n.rect))
    (hband0 : ∀ n ∈ nodes0, BandProp band n)
    (h : tileNodes c nodes0 = .ok out) :
    ∀ n ∈ out, BandProp band n := by
  rw [CanvasC1.tileNodes_eq_foldlM] at h
  have gen : ∀ (l : List Nat) (acc out : List Node),
      (∀ n ∈ acc, n.rect.Ordered ∧
        Rect.Contained (tileRect (CanvasC1.canvasTile c band)) (tileRect n.rect)) →
      (∀ n ∈ acc, BandProp band n) →
      l.foldlM (CanvasC1.tileStep c) acc = .ok out →
      ∀ n ∈ out, BandProp band n := by
    intro l
    induction l with
    | nil =>
      intro acc out hinv hband hfold
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hfold
      subst hfold
      exact hband
    | cons j js ih =>
      intro acc out hinv hband hfold
      simp only [List.foldlM] at hfold
      obtain ⟨mid, hmid, hrest⟩ := CanvasC1.except_bind_ok hfold
      exact ih mid out (CanvasC1.tileStep_invariant c band acc j mid hinv hmid)
        (tileStep_band c band acc j mid hpadX hpadY hbandc hinv hband hmid) hrest
  exact gen (dependencyOrder nodes0) nodes0 out hinv0 hband0 h

/-- Seed nodes satisfy the band property: only the root carries a real tile,
starting exactly at the title band. -/
private theorem ctx_seed_band (ctx : Ctx m) :
    ∀ n ∈ ctx.seed, BandProp (bandOf m) n := by
  intro n hn
  have hmem : n ∈ (assignSeries (aggregate (initialNodes m))).map
      (presetNode m (bandOf m)) := by
    rw [← ctx.hseedEq]
    exact hn
  rcases CanvasC1.seeded_rect_cases m n hmem with h | h
  · refine Or.inr (Or.inl ?_)
    rw [h]
    simp only [tileRect]
    omega
  · refine Or.inl ?_
    rw [h]
    simp only [tileRect]
    omega

/-- Kernel: every final tile lies at or below the title band, unless it is
degenerate. -/
theorem tile_below_band_or_degenerate' (ctx : Ctx m) (n : Node)
    (hn : n ∈ ctx.final) :
    bandOf m ≤ (tileRect n.rect).y ∨
      (tileRect n.rect).w ≤ 0 ∨ (tileRect n.rect).h ≤ 0 :=
  fold_band (constants m) (bandOf m) ctx.seed ctx.final
    (treemap_padX_ge m) (treemap_padY_ge m) (treemap_band_ge m)
    (ctx_seedinv (ctx := ctx)) (ctx_seed_band ctx) ctx.hfinal n hn
/-! ### The kernel bundle from the two open label kernels -/

/-- The C8b kernel bundle, given the two label kernels that are still OPEN
(`label_owner_cases` and `internal_label_header_band`).  The four tile kernels
are the theorems of this file. -/
theorem kernels_of_label_kernels (m : Model)
    (hOwner : ∀ (ctx : Ctx m) (result : Layered.FamilyResult),
      WellFormed m → Kinds.Treemap.layout m = .ok result →
      ∀ (l : Label), l ∈ result.scene.layoutDump.labels →
      l.rect = ⟨0, 0, 0, 0⟩ ∨
      (l.id = "title" ∧ bandOf m = (constants m).titleBand ∧
        Rect.Contained ⟨0, 0, (constants m).width, (constants m).titleBand⟩ l.rect) ∨
      ∃ n : Node, n ∈ ctx.final ∧ n.source.id = l.owner ∧
        (Rect.StrictInside (tileRect n.rect) l.rect ∨
          (n.source.role ≠ .group ∧ Rect.Contained (tileRect n.rect) l.rect)))
    (hBand : ∀ (ctx : Ctx m) (result : Layered.FamilyResult),
      WellFormed m → Kinds.Treemap.layout m = .ok result →
      ∀ (n : Node), n ∈ ctx.final → ∀ (l : Label),
      l ∈ result.scene.layoutDump.labels → n.source.id = l.owner →
      (∃ g : Node, g ∈ ctx.final ∧
        n.source.id ∈ boxAncestors m.boxes m.boxes.length g.source.id) →
      l.rect.y + l.rect.h ≤ (tileRect n.rect).y +
          (constants m).header + (constants m).padY ∧
        (Rect.StrictInside (tileRect n.rect) l.rect ∨ l.rect = ⟨0, 0, 0, 0⟩)) :
    Kernels m :=
  ⟨hOwner, tileRect_nonneg_or_degenerate', tile_below_band_or_degenerate',
    tile_strictInside_ancestor', descendant_tile_clear_of_header_label', hBand⟩

end Elegant.Treemap.C8b
