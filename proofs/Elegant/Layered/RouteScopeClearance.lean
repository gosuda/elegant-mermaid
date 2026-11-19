import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RouteTransport

set_option autoImplicit false

namespace Elegant.Layered

/-- A successful `componentRun` route misses the transported `boxRect` of every real node
outside its route scope: the node is not a chain endpoint and its declaration is not in the
cluster path of either endpoint node. The route points and the node rect are carried through
the same affine transport (`routePointTransport` on points, the matching `shiftRect` /
`orientRect` composition on rects), so the component-level avoidance of
`componentRun_route_avoids_nodes` transports unchanged. -/
theorem componentRun_exclusive_clear
    {P : PipelineImpl.Params} {cg : Graph} {run : PipelineImpl.Run}
    {labels : List PipelineImpl.MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid) (hd : (cg.edges.map (·.decl)).Nodup) (hS : PipelineImpl.CgShape cg)
    (hclear : PipelineImpl.FrameClearance run.proper run.layers run.xs)
    (hrun : PipelineImpl.componentRun P cg labels orderOptions = .ok run)
    {i : Nat} ( _hi : i < cg.edges.length) {rt : EdgeRoute}
    (hrt : run.routes[i]? = some rt)
    {i₀ i₁ v : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper rt.original).head? = some i₀)
    (hlast : (RouteImpl.edgesOf run.proper rt.original).getLast? = some i₁)
    (hv : v < run.proper.nodes.length)
    (hreal : RouteImpl.IsReal run.proper v)
    (hv0 : v ≠ (RouteImpl.edgeAt run.proper i₀).tail)
    (hv1 : v ≠ (RouteImpl.edgeAt run.proper i₁).head)
    ( _hscope0 : RouteImpl.nodeDecl run.proper v ∉
      ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map (·.node.clusterPath)).getD [])
    ( _hscope1 : RouteImpl.nodeDecl run.proper v ∉
      ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map (·.node.clusterPath)).getD [])
    (margin : Int) (d : Direction) (h : Int) (boxX boxY minX minY : Int) :
    ¬ Polyline.hitsRect
      (rt.points.map (routePointTransport margin d h boxX boxY minX minY))
      (PipelineImpl.shiftRect margin margin
        (PipelineImpl.orientRect d h
          (PipelineImpl.shiftRect (boxX - minX) (boxY - minY)
            (RouteImpl.boxRect run.proper run.xs run.ys v)))) := by
  have hrt_mem : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  have hmiss := componentRun_route_avoids_nodes hP hd hS hclear hrun rt hrt_mem i₀ i₁
    hfirst hlast v hv hreal hv0 hv1
  rw [← routePointTransport_eq]
  rw [← PipelineImpl.shiftRect_pack_normalize]
  rw [not_hitsRect_shift_orient_iff]
  rw [not_hitsRect_shift_iff]
  rw [not_hitsRect_shift_iff]
  exact hmiss

end Elegant.Layered
