import Elegant.Layered.ForeignSideFoldBoundProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Marking of edges interleaving a border chain edge.

Target: `foreignSideMarkingCrossed` below — the `ForeignSideMarkingCrossed`
residual of `ForeignSideFoldBoundProof`. In the executed pass context, every
edge strictly interleaving a border chain edge over the same layer pair is in
the `typeOneConflicts` conflict set.

Proof idea: case (1), the interleaving edge is not itself a border edge — the
pass marks exactly such edges (the `crossesAmong` scan finds the border witness
and the product of the two endpoint differences is negative after transporting
the pass-permuted coordinates back to the layer-check coordinates). Case (2),
the interleaving edge is a border edge — a border edge is never marked, so this
case needs two border edges to never interleave; that geometric fact is the one
residual left open (`ForeignBorderEdgesNoncrossing`).
-/

/-- The `crossesAmong` scan fires when a witness edge is present. -/
theorem crossesAmong_of_mem {p : Proper} {pos : Array Nat}
    {among : ProperEdge → Bool} {e f : ProperEdge} (hf : f ∈ p.edges)
    (hb : among f = true)
    (hr : (rk p.rank e.tail == rk p.rank f.tail) = true)
    (hprod : ((pos[e.tail]! : Int) - pos[f.tail]!) *
      ((pos[e.head]! : Int) - pos[f.head]!) < 0) :
    CoordsImpl.crossesAmong p pos among e = true := by
  unfold CoordsImpl.crossesAmong
  rw [List.any_eq_true]
  exact ⟨f, hf, by simp [hb, hr, decide_eq_true hprod]⟩

/-- Sign of a product with one positive and one negative factor. -/
theorem int_mul_neg_of_pos_of_neg {a b : Int} (ha : 0 < a) (hb : b < 0) :
    a * b < 0 := by
  have h1 : (0 : Int) < -b := by omega
  have h2 : (0 : Int) < a * (-b) := Int.mul_pos ha h1
  have h3 : a * (-b) = -(a * b) := Int.mul_neg a b
  omega

/-- Value tracking for one layer step: recorded triples hold the written positions. -/
theorem layerStep_val {pbase : Proper} {r : Nat} :
    ∀ (vs : List Nat) (j : Nat) (s s' : Array Nat × Array Bool)
      (T : List (Nat × Nat × Nat)),
      CoordsImpl.layerStep pbase pbase.nodes.length r j vs s = .ok s' →
      CoordsImpl.SInv pbase s T →
      (∀ t ∈ T, s.1[t.1]! = t.2.2) →
      (∀ t ∈ T ++ CoordsImpl.tr r j vs, s'.1[t.1]! = t.2.2) := by
  intro vs
  induction vs with
  | nil =>
    intro j s s' T h _hs hval
    simp only [CoordsImpl.layerStep, Except.ok.injEq] at h
    subst h
    simpa [CoordsImpl.tr] using hval
  | cons v vs ih =>
    intro j s s' T h hs hval
    simp only [CoordsImpl.layerStep] at h
    by_cases hc : (pbase.nodes.length ≤ v ∨ s.2[v]! ∨
      rk pbase.rank v ≠ (r : Int))
    · rw [ite_eq_left hc] at h
      cases h
    · rw [ite_eq_right hc] at h
      have hsinv := CoordsImpl.sinv_step (j := j) hs hc
      have hsv : s.2[v]! = false := by
        have hc2 := hc
        simp only [not_or] at hc2
        simpa using hc2.2.1
      have hval' : ∀ t ∈ T ++ [(v, r, j)], (s.1.set! v j)[t.1]! = t.2.2 := by
        intro t ht
        rcases List.mem_append.mp ht with htT | ht1
        · have hne : v ≠ t.1 := by
            intro heq
            have hseen := (hs.ok t htT).2.2
            rw [← heq] at hseen
            rw [hsv] at hseen
            exact Bool.false_ne_true hseen
          rw [Array.getElem!_set!_ne _ _ _ _ hne]
          exact hval t htT
        · simp at ht1
          subst ht1
          show (s.1.set! v j)[v]! = j
          exact Array.getElem!_set!_self _ _ _ (by
            rw [hs.size1]
            have hle : ¬ pbase.nodes.length ≤ v := fun hle => hc (Or.inl hle)
            omega)
      have hstep := ih (j + 1) _ s' (T ++ [(v, r, j)]) h hsinv hval'
      simpa [CoordsImpl.tr, List.append_assoc] using hstep

/-- Value tracking across layers. -/
theorem layersStep_val {pbase : Proper} (ls : List (List Nat)) :
    ∀ (r : Nat) (s s' : Array Nat × Array Bool) (T : List (Nat × Nat × Nat)),
      CoordsImpl.layersStep pbase pbase.nodes.length r ls s = .ok s' →
      CoordsImpl.SInv pbase s T →
      (∀ t ∈ T, s.1[t.1]! = t.2.2) →
      (∀ t ∈ T ++ CoordsImpl.trs r ls, s'.1[t.1]! = t.2.2) := by
  induction ls with
  | nil =>
    intro r s s' T h _hs hval
    simp only [CoordsImpl.layersStep, Except.ok.injEq] at h
    subst h
    simpa [CoordsImpl.trs] using hval
  | cons l ls ih =>
    intro r s s' T h hs hval
    simp only [CoordsImpl.layersStep] at h
    cases h1 : CoordsImpl.layerStep pbase pbase.nodes.length r 0 l s with
    | error e =>
      rw [h1] at h
      cases h
    | ok s1 =>
      rw [h1] at h
      have h2sinv := CoordsImpl.layerStep_spec r l 0 s s1 T h1 hs
      have h2val := layerStep_val l 0 s s1 T h1 hs hval
      have h3 := ih (r + 1) s1 s' (T ++ CoordsImpl.tr r 0 l) h h2sinv h2val
      simpa [CoordsImpl.trs, List.append_assoc] using h3

/-- The layer-check positions are within-layer indices. -/
theorem layerPositions_val {pbase : Proper} {layers : List (List Nat)}
    {pos : Array Nat} (h : CoordsImpl.layerPositions pbase layers = .ok pos)
    {i : Nat} {l : List Nat} (hi : layers[i]? = some l)
    {j v : Nat} (hj : l[j]? = some v) : pos[v]! = j := by
  unfold CoordsImpl.layerPositions at h
  cases hs : CoordsImpl.layersStep pbase pbase.nodes.length 0 layers
      (Array.replicate pbase.nodes.length 0,
        Array.replicate pbase.nodes.length false) with
  | error e =>
    rw [hs] at h
    cases h
  | ok s =>
    rw [hs] at h
    simp only [] at h
    by_cases hany : s.2.any (fun b => !b) = true
    · rw [ite_eq_left hany] at h
      cases h
    · have hS := layersStep_val layers 0 _ s [] hs (CoordsImpl.sinv_init pbase)
        (by simp)
      simp only [List.nil_append] at hS
      have hmem : (v, i, j) ∈ CoordsImpl.trs 0 layers := by
        simpa using CoordsImpl.mem_trs layers 0 i l j v hi hj
      have hval := hS _ hmem
      have hps : s.1 = pos := by
        rw [ite_eq_right hany] at h
        simp only [Except.ok.injEq] at h
        exact h
      rw [← hps]
      exact hval

 /-- Pass-permuted coordinates of one node in terms of the layer-check data. -/
 theorem nodeTransport {P : Params} {run : Run} {pos : Array Nat} {k : Nat}
     (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
     (hL : CoordsImpl.Lay (sideCtx P run pos k))
     {v : Nat} (hv : v ∈ run.layers.flatten) :
     ((sideCtx P run pos k).rank[v]! : Int) =
         (if 2 ≤ k then (run.layers.length : Int) - 1 - rk (sideBase run).rank v
           else rk (sideBase run).rank v) ∧
       ∃ (l : List Nat) (i j : Nat),
         run.layers[i]? = some l ∧ l[j]? = some v ∧
           (sideCtx P run pos k).pos[v]! =
             (if k % 2 = 1 then l.length - 1 - j else j) ∧
           pos[v]! = j ∧ rk (sideBase run).rank v = (i : Int) := by
   obtain ⟨l, hll, hvmem⟩ := List.mem_flatten.mp hv
   obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hll
   obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
   have hlp_pos : CoordsImpl.layerPositions (sideBase run) run.layers = .ok pos := by
     unfold CoordsImpl.checkLayers at hpos
     split at hpos
     · simp at hpos
     · split at hpos
       · simp at hpos
       · next _hs =>
         split at hpos
         · simp at hpos
         · next _hr =>
           split at hpos
           · simp at hpos
           · next pos' hlp' =>
             split at hpos
             · simp at hpos
             · next _hed =>
               simp only [Except.ok.injEq] at hpos
               rw [← hpos]
               exact hlp'
   have hrk : rk (sideBase run).rank v = (i : Int) :=
     (CoordsImpl.layerPositions_spec hlp_pos).2.1 i l v hi hvmem
   have hval : pos[v]! = j := layerPositions_val hlp_pos hi hj
   have hiL : i < run.layers.length := (List.getElem?_eq_some_iff.mp hi).1
   have hctx : (sideCtx P run pos k).layers =
       CoordsImpl.passLayers run.layers k := rfl
   have hrank : ((sideCtx P run pos k).rank[v]! : Int) =
       (if 2 ≤ k then (run.layers.length : Int) - 1 - rk (sideBase run).rank v
         else rk (sideBase run).rank v) := by
     obtain ⟨l0, hl0, hiff⟩ := CoordsImpl.passLayers_get run.layers k hi
     obtain ⟨jj, hjj⟩ := List.mem_iff_getElem?.mp ((hiff v).mpr hvmem)
     have hget : (sideCtx P run pos k).layers[if 2 ≤ k then run.layers.length - 1 - i
         else i]? = some l0 := by
       rw [hctx]
       exact hl0
     have hidx := hL.idx _ l0 jj v hget hjj
     rw [hidx.1, hrk]
     by_cases hk : 2 ≤ k
     · rw [ite_eq_left hk]
       omega
     · rw [ite_eq_right hk]
       omega
   have hjlt : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
   have hrev : (run.layers.reverse)[run.layers.length - 1 - i]? = some l := by
     rw [List.getElem?_reverse (by omega)]
     have heq : run.layers.length - 1 - (run.layers.length - 1 - i) = i := by
       omega
     rw [heq]
     exact hi
   refine ⟨hrank, l, i, j, hi, hj, ?_, hval, hrk⟩
   by_cases hkodd : k % 2 = 1
   · by_cases hk2 : 2 ≤ k
     · have hcollapse : ((some l).map fun l =>
         if k % 2 = 1 then l.reverse else l) = some l.reverse := by
         show some (if k % 2 = 1 then l.reverse else l) = some l.reverse
         rw [ite_eq_left hkodd]
       have hget : (sideCtx P run pos k).layers[run.layers.length - 1 - i]? =
           some l.reverse := by
         rw [hctx]
         show (((if 2 ≤ k then run.layers.reverse else run.layers).map
           fun l => if k % 2 = 1 then l.reverse else l))[run.layers.length - 1 - i]? =
           some l.reverse
         rw [ite_eq_left hk2, List.getElem?_map, hrev, hcollapse]
       have hvalr : l.reverse[l.length - 1 - j]? = some v := by
         rw [List.getElem?_reverse (by omega)]
         have heq : l.length - 1 - (l.length - 1 - j) = j := by omega
         rw [heq]
         exact hj
       have hidx := hL.idx _ l.reverse (l.length - 1 - j) v hget hvalr
       rw [ite_eq_left hkodd]
       exact hidx.2
     · have hcollapse : ((some l).map fun l =>
         if k % 2 = 1 then l.reverse else l) = some l.reverse := by
         show some (if k % 2 = 1 then l.reverse else l) = some l.reverse
         rw [ite_eq_left hkodd]
       have hget : (sideCtx P run pos k).layers[i]? = some l.reverse := by
         rw [hctx]
         show (((if 2 ≤ k then run.layers.reverse else run.layers).map
           fun l => if k % 2 = 1 then l.reverse else l))[i]? = some l.reverse
         rw [ite_eq_right hk2, List.getElem?_map, hi, hcollapse]
       have hvalr : l.reverse[l.length - 1 - j]? = some v := by
         rw [List.getElem?_reverse (by omega)]
         have heq : l.length - 1 - (l.length - 1 - j) = j := by omega
         rw [heq]
         exact hj
       have hidx := hL.idx _ l.reverse (l.length - 1 - j) v hget hvalr
       rw [ite_eq_left hkodd]
       exact hidx.2
   · by_cases hk2 : 2 ≤ k
     · have hcollapseE : ((some l).map fun l =>
         if k % 2 = 1 then l.reverse else l) = some l := by
         show some (if k % 2 = 1 then l.reverse else l) = some l
         rw [ite_eq_right hkodd]
       have hget : (sideCtx P run pos k).layers[run.layers.length - 1 - i]? =
           some l := by
         rw [hctx]
         show (((if 2 ≤ k then run.layers.reverse else run.layers).map
           fun l => if k % 2 = 1 then l.reverse else l))[run.layers.length - 1 - i]? =
           some l
         rw [ite_eq_left hk2, List.getElem?_map, hrev, hcollapseE]
       have hidx := hL.idx _ l j v hget hj
       rw [ite_eq_right hkodd]
       exact hidx.2
     · have hcollapseE : ((some l).map fun l =>
         if k % 2 = 1 then l.reverse else l) = some l := by
         show some (if k % 2 = 1 then l.reverse else l) = some l
         rw [ite_eq_right hkodd]
       have hget : (sideCtx P run pos k).layers[i]? = some l := by
         rw [hctx]
         show (((if 2 ≤ k then run.layers.reverse else run.layers).map
           fun l => if k % 2 = 1 then l.reverse else l))[i]? = some l
         rw [ite_eq_right hk2, List.getElem?_map, hi, hcollapseE]
       have hidx := hL.idx _ l j v hget hj
       rw [ite_eq_right hkodd]
       exact hidx.2

/-- Case (1): a non-border edge interleaving a border edge is marked. -/
theorem marked_of_interleave_noborder {P : Params} {run : Run} {pos : Array Nat}
    {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {e f w x a b : Nat}
    (he : e < (sideCtx P run pos k).edges.size)
    (hf : f < (sideCtx P run pos k).edges.size)
    (he_orient : ((sideCtx P run pos k).edges[e]!.tail = w ∧
        (sideCtx P run pos k).edges[e]!.head = x ∨
      (sideCtx P run pos k).edges[e]!.tail = x ∧
        (sideCtx P run pos k).edges[e]!.head = w))
    (hf_orient : ((sideCtx P run pos k).edges[f]!.tail = a ∧
        (sideCtx P run pos k).edges[f]!.head = b ∨
      (sideCtx P run pos k).edges[f]!.tail = b ∧
        (sideCtx P run pos k).edges[f]!.head = a))
    (hfb : CoordsImpl.borderChain (sideBase run)
      ((sideCtx P run pos k).edges[f]!) = true)
    (hne_b : CoordsImpl.borderChain (sideBase run)
      ((sideCtx P run pos k).edges[e]!) = false)
    (hr1 : (sideCtx P run pos k).rank[w]! + 1 = (sideCtx P run pos k).rank[x]!)
    (hr2 : (sideCtx P run pos k).rank[a]! + 1 = (sideCtx P run pos k).rank[b]!)
    (hr3 : (sideCtx P run pos k).rank[x]! = (sideCtx P run pos k).rank[b]!)
    (hp1 : ((sideCtx P run pos k).pos[a]! : Int) <
      ((sideCtx P run pos k).pos[w]! : Int))
    (hp2 : ((sideCtx P run pos k).pos[x]! : Int) <
      ((sideCtx P run pos k).pos[b]! : Int)) :
    (sideCtx P run pos k).marked[e]! = true := by
  obtain ⟨hL, hE⟩ :=
    Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos
  obtain ⟨_, _, hce⟩ := CoordsImpl.checkLayers_parts hpos
  have hedges := CoordsImpl.checkEdges_spec hce
  have hEeq : (sideCtx P run pos k).edges = (sideBase run).edges.toArray := rfl
  have hlen_e : e < (sideBase run).edges.length := by
    have h1 := he
    rw [hEeq] at h1
    simpa using h1
  have hlen_f : f < (sideBase run).edges.length := by
    have h1 := hf
    rw [hEeq] at h1
    simpa using h1
  have hEe_mem : (sideCtx P run pos k).edges[e]! ∈ (sideBase run).edges := by
    rw [hEeq]
    rw [getElem!_pos _ e (by simpa using hlen_e)]
    exact List.getElem_mem _
  have hEf_mem : (sideCtx P run pos k).edges[f]! ∈ (sideBase run).edges := by
    rw [hEeq]
    rw [getElem!_pos _ f (by simpa using hlen_f)]
    exact List.getElem_mem _
  obtain ⟨-, -, hce_e⟩ := hedges _ hEe_mem
  obtain ⟨-, -, hce_f⟩ := hedges _ hEf_mem
  obtain ⟨hte_fl, hhe_fl, -⟩ := hE e he
  obtain ⟨htf_fl, hhf_fl, -⟩ := hE f hf
  have hctxL : (sideCtx P run pos k).layers =
      CoordsImpl.passLayers run.layers k := rfl
  have hperm := CoordsImpl.passLayers_perm run.layers k
  have torun : ∀ v : Nat, v ∈ (sideCtx P run pos k).layers.flatten →
      v ∈ run.layers.flatten := by
    intro v hv
    rw [hctxL] at hv
    exact hperm.mem_iff.mp hv
  have hmem_wx : w ∈ (sideCtx P run pos k).layers.flatten ∧
      x ∈ (sideCtx P run pos k).layers.flatten := by
    rcases he_orient with ⟨hte_w, hhe_x⟩ | ⟨hte_x, hhe_w⟩
    · exact ⟨by rw [← hte_w]; exact hte_fl, by rw [← hhe_x]; exact hhe_fl⟩
    · exact ⟨by rw [← hhe_w]; exact hhe_fl, by rw [← hte_x]; exact hte_fl⟩
  have hmem_ab : a ∈ (sideCtx P run pos k).layers.flatten ∧
      b ∈ (sideCtx P run pos k).layers.flatten := by
    rcases hf_orient with ⟨hta_a, hha_b⟩ | ⟨hta_b, hha_a⟩
    · exact ⟨by rw [← hta_a]; exact htf_fl, by rw [← hha_b]; exact hhf_fl⟩
    · exact ⟨by rw [← hha_a]; exact hhf_fl, by rw [← hta_b]; exact htf_fl⟩
  obtain ⟨hrank_w, lw, iw, jw, hiw, -, hposw, hvalw, hrkw⟩ :=
    nodeTransport hpos hL (torun w hmem_wx.1)
  obtain ⟨hrank_x, lx, ix, jx, hix, -, hposx, hvalx, hrkx⟩ :=
    nodeTransport hpos hL (torun x hmem_wx.2)
  obtain ⟨hrank_a, la, ia, ja, hia, -, hposa, hvala, hrka⟩ :=
    nodeTransport hpos hL (torun a hmem_ab.1)
  obtain ⟨hrank_b, lb, ib, jb, hib, -, hposb, hvalb, hrkb⟩ :=
    nodeTransport hpos hL (torun b hmem_ab.2)
  have hEedge : (sideBase run).edges[e]'hlen_e =
      (sideCtx P run pos k).edges[e]! := by
    rw [hEeq, getElem!_pos _ e (by simpa using hlen_e),
      List.getElem_toArray (by simpa using hlen_e)]
  have hne_arr : CoordsImpl.borderChain (sideBase run)
      ((sideBase run).edges[e]'hlen_e) = false := by
    rw [hEedge]
    exact hne_b
  -- Entry rewrite shared by all orientation leaves.
  have hentry : ∀ hscan : CoordsImpl.crossesAmong (sideBase run) pos
      (CoordsImpl.borderChain (sideBase run))
      ((sideCtx P run pos k).edges[e]!) = true,
      (sideCtx P run pos k).marked[e]! = true := by
    intro hscan
    have hscan_arr : CoordsImpl.crossesAmong (sideBase run) pos
        (CoordsImpl.borderChain (sideBase run))
        ((sideBase run).edges[e]'hlen_e) = true := by
      rw [hEedge]
      exact hscan
    have hs : e < ((sideBase run).edges.map fun e =>
         !CoordsImpl.borderChain (sideBase run) e &&
           (CoordsImpl.crossesAmong (sideBase run) pos
             (CoordsImpl.borderChain (sideBase run)) e ||
             (!CoordsImpl.innerEdge (sideBase run) e &&
               CoordsImpl.crossesInner (sideBase run) pos e))).toArray.size := by
       simpa using hlen_e
    have hMeq : (sideCtx P run pos k).marked =
        CoordsImpl.typeOneConflicts (sideBase run) pos := rfl
    rw [hMeq]
    unfold CoordsImpl.typeOneConflicts
    rw [getElem!_pos _ e hs, List.getElem_toArray (by simpa using hs),
      List.getElem_map]
    simp [hne_arr, hscan_arr]
  -- Shared parity resolution, then rank resolution and layer unification per
  -- mirror case, then orientation leaves: omega closes the linear facts
  -- (vacuously in inconsistent orientation worlds) and the sign lemma closes
  -- the product.
  by_cases hkodd : k % 2 = 1
  · -- Odd passes reverse within-layer order.
     rw [ite_eq_left hkodd] at hposw hposx hposa hposb
     by_cases hk2 : 2 ≤ k
     · simp only [hk2, ite_true] at hrank_w hrank_x hrank_a hrank_b
       have hrk_wa : rk (sideBase run).rank w = rk (sideBase run).rank a := by
         omega
       have hiw_ia : iw = ia := by omega
       subst hiw_ia
       have hll_wa : lw = la := by simpa using hiw.symm.trans hia
       subst hll_wa
       have hrk_xb : rk (sideBase run).rank x = rk (sideBase run).rank b := by
         omega
       have hix_ib : ix = ib := by omega
       subst hix_ib
       have hll_xb : lx = lb := by simpa using hix.symm.trans hib
       subst hll_xb
       rcases he_orient with ⟨hte_w, hhe_x⟩ | ⟨hte_x, hhe_w⟩ <;>
         rcases hf_orient with ⟨hta_a, hha_b⟩ | ⟨hta_b, hha_a⟩
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[w]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[x]! : Int) - (pos[b]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[w]! : Int) - pos[a]!) *
             ((pos[x]! : Int) - pos[b]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[w]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[x]! : Int) - (pos[a]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[w]! : Int) - pos[b]!) *
             ((pos[x]! : Int) - pos[a]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[x]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[w]! : Int) - (pos[b]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[x]! : Int) - pos[a]!) *
             ((pos[w]! : Int) - pos[b]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[x]! : Int) - (pos[b]! : Int)) := by omega
         have s2 : ((pos[w]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have hprod : ((pos[x]! : Int) - pos[b]!) *
             ((pos[w]! : Int) - pos[a]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
     · simp only [hk2, ite_false] at hrank_w hrank_x hrank_a hrank_b
       have hrk_wa : rk (sideBase run).rank w = rk (sideBase run).rank a := by
         omega
       have hiw_ia : iw = ia := by omega
       subst hiw_ia
       have hll_wa : lw = la := by simpa using hiw.symm.trans hia
       subst hll_wa
       have hrk_xb : rk (sideBase run).rank x = rk (sideBase run).rank b := by
         omega
       have hix_ib : ix = ib := by omega
       subst hix_ib
       have hll_xb : lx = lb := by simpa using hix.symm.trans hib
       subst hll_xb
       rcases he_orient with ⟨hte_w, hhe_x⟩ | ⟨hte_x, hhe_w⟩ <;>
         rcases hf_orient with ⟨hta_a, hha_b⟩ | ⟨hta_b, hha_a⟩
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[w]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[x]! : Int) - (pos[b]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[w]! : Int) - pos[a]!) *
             ((pos[x]! : Int) - pos[b]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[w]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[x]! : Int) - (pos[a]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[w]! : Int) - pos[b]!) *
             ((pos[x]! : Int) - pos[a]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[x]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[w]! : Int) - (pos[b]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[x]! : Int) - pos[a]!) *
             ((pos[w]! : Int) - pos[b]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[x]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[w]! : Int) - (pos[a]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[x]! : Int) - pos[b]!) *
             ((pos[w]! : Int) - pos[a]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
  · -- Even passes keep within-layer order.
     rw [ite_eq_right hkodd] at hposw hposx hposa hposb
     by_cases hk2 : 2 ≤ k
     · simp only [hk2, ite_true] at hrank_w hrank_x hrank_a hrank_b
       have hrk_wa : rk (sideBase run).rank w = rk (sideBase run).rank a := by
         omega
       have hiw_ia : iw = ia := by omega
       subst hiw_ia
       have hll_wa : lw = la := by simpa using hiw.symm.trans hia
       subst hll_wa
       have hrk_xb : rk (sideBase run).rank x = rk (sideBase run).rank b := by
         omega
       have hix_ib : ix = ib := by omega
       subst hix_ib
       have hll_xb : lx = lb := by simpa using hix.symm.trans hib
       subst hll_xb
       rcases he_orient with ⟨hte_w, hhe_x⟩ | ⟨hte_x, hhe_w⟩ <;>
         rcases hf_orient with ⟨hta_a, hha_b⟩ | ⟨hta_b, hha_a⟩
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[w]! : Int) - (pos[a]! : Int)) := by omega
         have s2 : ((pos[x]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have hprod : ((pos[w]! : Int) - pos[a]!) *
             ((pos[x]! : Int) - pos[b]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[w]! : Int) - (pos[b]! : Int)) := by omega
         have s2 : ((pos[x]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have hprod : ((pos[w]! : Int) - pos[b]!) *
             ((pos[x]! : Int) - pos[a]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[x]! : Int) - (pos[a]! : Int)) := by omega
         have s2 : ((pos[w]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have hprod : ((pos[x]! : Int) - pos[a]!) *
             ((pos[w]! : Int) - pos[b]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : ((pos[x]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have s2 : (0 : Int) < ((pos[w]! : Int) - (pos[a]! : Int)) := by omega
         have hbase := int_mul_neg_of_pos_of_neg s2 s1
         have hprod : ((pos[x]! : Int) - pos[b]!) *
             ((pos[w]! : Int) - pos[a]!) < 0 := by
           rw [Int.mul_comm]
           exact hbase
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
     · simp only [hk2, ite_false] at hrank_w hrank_x hrank_a hrank_b
       have hrk_wa : rk (sideBase run).rank w = rk (sideBase run).rank a := by
         omega
       have hiw_ia : iw = ia := by omega
       subst hiw_ia
       have hll_wa : lw = la := by simpa using hiw.symm.trans hia
       subst hll_wa
       have hrk_xb : rk (sideBase run).rank x = rk (sideBase run).rank b := by
         omega
       have hix_ib : ix = ib := by omega
       subst hix_ib
       have hll_xb : lx = lb := by simpa using hix.symm.trans hib
       subst hll_xb
       rcases he_orient with ⟨hte_w, hhe_x⟩ | ⟨hte_x, hhe_w⟩ <;>
         rcases hf_orient with ⟨hta_a, hha_b⟩ | ⟨hta_b, hha_a⟩
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[w]! : Int) - (pos[a]! : Int)) := by omega
         have s2 : ((pos[x]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have hprod : ((pos[w]! : Int) - pos[a]!) *
             ((pos[x]! : Int) - pos[b]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_w, hhe_x] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank w = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_w, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[w]! : Int) - (pos[b]! : Int)) := by omega
         have s2 : ((pos[x]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have hprod : ((pos[w]! : Int) - pos[b]!) *
             ((pos[x]! : Int) - pos[a]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_w, hhe_x, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_a, hha_b] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank a := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_a]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[x]! : Int) - (pos[a]! : Int)) := by omega
         have s2 : ((pos[w]! : Int) - (pos[b]! : Int)) < 0 := by omega
         have hprod : ((pos[x]! : Int) - pos[a]!) *
             ((pos[w]! : Int) - pos[b]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_a, hha_b]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)
       · rw [hte_x, hhe_w] at hce_e
         rw [hta_b, hha_a] at hce_f
         have htrk : rk (sideBase run).rank x = rk (sideBase run).rank b := by
           omega
         have htrk_edge : rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) =
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail) := by
           rw [hte_x, hta_b]
           exact htrk
         have hrk_beq : (rk (sideBase run).rank
             ((sideCtx P run pos k).edges[e]!.tail) ==
             rk (sideBase run).rank
               ((sideCtx P run pos k).edges[f]!.tail)) = true := by
           simp [htrk_edge]
         have s1 : (0 : Int) < ((pos[x]! : Int) - (pos[b]! : Int)) := by omega
         have s2 : ((pos[w]! : Int) - (pos[a]! : Int)) < 0 := by omega
         have hprod : ((pos[x]! : Int) - pos[b]!) *
             ((pos[w]! : Int) - pos[a]!) < 0 :=
           int_mul_neg_of_pos_of_neg s1 s2
         have hprod_edge : ((pos[(sideCtx P run pos k).edges[e]!.tail]! : Int) -
             pos[(sideCtx P run pos k).edges[f]!.tail]!) *
             ((pos[(sideCtx P run pos k).edges[e]!.head]! : Int) -
               pos[(sideCtx P run pos k).edges[f]!.head]!) < 0 := by
           rw [hte_x, hhe_w, hta_b, hha_a]
           exact hprod
         exact hentry (crossesAmong_of_mem hEf_mem hfb hrk_beq hprod_edge)

/-- Border-border non-crossing residual (one phase: the executed
`borderAlignment` chain edges). Two border chain edges over one layer pair never
strictly interleave in an executed run. This is the only unproved case of
`foreignSideMarkingCrossed`: a border edge is never marked by
`typeOneConflicts`, so the marking conclusion needs the interleave hypotheses
to be contradictory. -/
def ForeignBorderEdgesNoncrossing (P : Params) (run : Run) (pos : Array Nat)
    (k : Nat) : Prop :=
  ∀ (e f w x a b : Nat),
    e < (sideCtx P run pos k).edges.size →
    f < (sideCtx P run pos k).edges.size →
    ((sideCtx P run pos k).edges[e]!.tail = w ∧
        (sideCtx P run pos k).edges[e]!.head = x ∨
      (sideCtx P run pos k).edges[e]!.tail = x ∧
        (sideCtx P run pos k).edges[e]!.head = w) →
    ((sideCtx P run pos k).edges[f]!.tail = a ∧
        (sideCtx P run pos k).edges[f]!.head = b ∨
      (sideCtx P run pos k).edges[f]!.tail = b ∧
        (sideCtx P run pos k).edges[f]!.head = a) →
    CoordsImpl.borderChain (sideBase run)
      ((sideCtx P run pos k).edges[e]!) = true →
    CoordsImpl.borderChain (sideBase run)
      ((sideCtx P run pos k).edges[f]!) = true →
    (sideCtx P run pos k).rank[w]! + 1 = (sideCtx P run pos k).rank[x]! →
    (sideCtx P run pos k).rank[a]! + 1 = (sideCtx P run pos k).rank[b]! →
    (sideCtx P run pos k).rank[x]! = (sideCtx P run pos k).rank[b]! →
    ((sideCtx P run pos k).pos[a]! : Int) <
      ((sideCtx P run pos k).pos[w]! : Int) →
    ((sideCtx P run pos k).pos[x]! : Int) <
      ((sideCtx P run pos k).pos[b]! : Int) →
    False

/-- The marking-pass residual: every edge interleaving a border chain edge over
the same layer pair is marked. Case (1) is proved above; case (2) follows from
the border-border non-crossing residual. -/
theorem foreignSideMarkingCrossed {P : Params} {run : Run} {pos : Array Nat}
    {k : Nat}
    (_hrun : ∃ (cg : Graph) (labels : List MeasuredLabel)
      (orderOptions : OrderOptions),
      componentRun P cg labels orderOptions = .ok run)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (_hk : k < 4)
    (hcross : ForeignBorderEdgesNoncrossing P run pos k) :
    ForeignSideMarkingCrossed P run pos k := by
  unfold ForeignSideMarkingCrossed
  intro e f w x a b he hf he_or hf_or hfb hr1 hr2 hr3 hp1 hp2
  by_cases hbe : CoordsImpl.borderChain (sideBase run)
      ((sideCtx P run pos k).edges[e]!) = true
  · exact False.elim
      (hcross e f w x a b he hf he_or hf_or hbe hfb hr1 hr2 hr3 hp1 hp2)
  · exact marked_of_interleave_noborder hpos he hf he_or hf_or hfb
       (Bool.eq_false_of_ne_true hbe) hr1 hr2 hr3 hp1 hp2

/-- The alignment-fold bound with the marking hypothesis discharged, keeping the
chain-shape hypothesis and the border-border non-crossing residual. -/
theorem foreignSideFoldBound' {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat} {k : Nat}
    (hrun : ∃ (cg : Graph) (labels : List MeasuredLabel)
      (orderOptions : OrderOptions),
      componentRun P cg labels orderOptions = .ok run)
    (_hside : side = -1 ∨ side = 1) (hk : k < 4)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hshape : ForeignSideChainShape P run side decl pos k)
    (hcross : ForeignBorderEdgesNoncrossing P run pos k) :
    ForeignSideFoldBound P run side decl pos k :=
  foreignSideFoldBound hrun _hside hk hpos hshape
    (foreignSideMarkingCrossed hrun hpos hk hcross)

end Elegant.Layered.PipelineImpl
