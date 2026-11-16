import Elegant.TreeValid

set_option autoImplicit false

namespace Elegant
namespace Tree

/-- Normalization translates every box and route by the same vector. -/
theorem normalize_records {margin : Int} {l out : Layout} {canvas : Size}
    (h : normalize margin l = .ok (canvas, out)) :
    ∃ dx dy,
      out.boxes = l.boxes.map (fun r => r.translateRaw dx dy) ∧
      out.routes = l.routes.map (fun pts => pts.map fun p => ⟨p.x + dx, p.y + dy⟩) := by
  obtain ⟨dx, dy, rfl⟩ := normalize_translate h
  exact ⟨dx, dy, rfl, rfl⟩

theorem normalized_length {margin : Int} {l out : Layout} {canvas : Size}
    (h : normalize margin l = .ok (canvas, out)) : out.boxes.length = l.boxes.length := by
  obtain ⟨dx, dy, hb, _⟩ := normalize_records h
  rw [hb, List.length_map]

theorem normalized_disjoint {ns : List Node} {g : Gaps} {l out : Layout} {canvas : Size}
    {margin : Int} (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns)
    (h0 : 0 < ns.length) (hl : layoutRaw ns g = .ok l)
    (hn : normalize margin l = .ok (canvas, out)) {i j : Nat} {a b : Rect}
    (ha : out.boxes[i]? = some a) (hb : out.boxes[j]? = some b) (hij : i ≠ j) :
    Disjoint a b := by
  obtain ⟨dx, dy, hboxes, _⟩ := normalize_records hn
  rw [hboxes, List.getElem?_map, Option.map_eq_some_iff] at ha hb
  obtain ⟨a0, ha0, rfl⟩ := ha
  obtain ⟨b0, hb0, rfl⟩ := hb
  exact disjoint_translate_raw (layoutRaw_disjoint hL hs hv h0 hl ha0 hb0 hij) dx dy

theorem normalized_route_ports {ns : List Node} {g : Gaps} {l out : Layout} {canvas : Size}
    {margin : Int} (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling) (hv : Valid ns)
    (h0 : 0 < ns.length) (hl : layoutRaw ns g = .ok l)
    (hn : normalize margin l = .ok (canvas, out)) {i p : Nat} (hi : i < ns.length)
    (hp : parentOf ns i = some p) :
    ∃ pts a b pr cr, out.routes[i]? = some pts ∧
      out.boxes[p]? = some pr ∧ out.boxes[i]? = some cr ∧
      pts.head? = some a ∧ pts.getLast? = some b ∧
      Validator.onBoundary a pr ∧ Validator.onBoundary b cr ∧
      Polyline.isOrthogonal pts = true := by
  obtain ⟨dx, dy, hboxes, hroutes⟩ := normalize_records hn
  obtain ⟨pts, a, b, pr, cr, hr, hpr, hcr, ha, hb, hpa, hpb, ho⟩ :=
    raw_route_ports hL hs hv h0 hl hi hp
  refine ⟨pts.map (fun q => ⟨q.x + dx, q.y + dy⟩),
    ⟨a.x + dx, a.y + dy⟩, ⟨b.x + dx, b.y + dy⟩,
    pr.translateRaw dx dy, cr.translateRaw dx dy, ?_, ?_, ?_, ?_, ?_,
    boundary_translate_raw hpa dx dy, boundary_translate_raw hpb dx dy, ?_⟩
  · simp [hroutes, hr]
  · simp [hboxes, hpr]
  · simp [hboxes, hcr]
  · simp [List.head?_map, ha]
  · simp [List.getLast?_map, hb]
  · rw [orthogonal_translate, ho]

theorem normalized_route_clear {ns : List Node} {g : Gaps} {l out : Layout}
    {canvas : Size} {margin : Int} (hL : 0 ≤ g.level) (hs : 1 ≤ g.sibling)
    (hv : Valid ns) (h0 : 0 < ns.length) (hl : layoutRaw ns g = .ok l)
    (hn : normalize margin l = .ok (canvas, out)) {i p k : Nat} (hi : i < ns.length)
    (hp : parentOf ns i = some p) {pts : List Point} (hr : out.routes[i]? = some pts)
    {r : Rect} (hb : out.boxes[k]? = some r) (hkp : k ≠ p) (hki : k ≠ i) :
    ¬ Polyline.hitsRect pts r := by
  obtain ⟨dx, dy, hboxes, hroutes⟩ := normalize_records hn
  rw [hroutes, List.getElem?_map, Option.map_eq_some_iff] at hr
  rw [hboxes, List.getElem?_map, Option.map_eq_some_iff] at hb
  obtain ⟨pts0, hr0, rfl⟩ := hr
  obtain ⟨r0, hb0, rfl⟩ := hb
  exact not_hits_of_aside ((raw_route_aside hL hs hv h0 hl hi hp hr0 hb0 hkp hki).map_translate dx dy)

end Tree
end Elegant
