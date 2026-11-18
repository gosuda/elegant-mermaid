package chart

import (
	"context"
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func Layout(ctx context.Context, m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	if err := ctx.Err(); err != nil {
		return scene.Scene{}, nil, err
	}
	if !hasChartPayload(m) {
		return scene.Scene{}, nil, fmt.Errorf("chart layout: unsupported kind %q", m.Kind)
	}
	switch m.Kind {
	case chartmodel.KindGantt:
		return layoutGantt(m, o)
	case chartmodel.KindRadar:
		return layoutRadar(m, o)
	case chartmodel.KindTreemap:
		return layoutTreemap(m, o)
	case chartmodel.KindPie:
		return layoutPie(m, o)
	case chartmodel.KindVenn:
		return layoutVenn(m, o)
	case chartmodel.KindSankey:
		return layoutSankey(m, o)
	default:
		return layoutXY(m, o)
	}
}

type Skeleton struct {
	Boxes  []scene.Box
	Labels []scene.Label
}

func ModelSkeleton(m *chartmodel.Chart) (Skeleton, error) {
	if !hasChartPayload(m) {
		return Skeleton{}, fmt.Errorf("chart layout: unsupported kind %q", m.Kind)
	}
	switch m.Kind {
	case chartmodel.KindGantt:
		return ganttSkeleton(m)
	case chartmodel.KindRadar:
		return radarSkeleton(m)
	case chartmodel.KindTreemap:
		return treemapSkeleton(m)
	case chartmodel.KindPie:
		return pieSkeleton(m)
	case chartmodel.KindVenn:
		return vennModelSkeleton(m)
	case chartmodel.KindSankey:
		return sankeySkeleton(m), nil
	}
	p, err := newXYPlan(m, scene.Options{})
	if err != nil {
		return Skeleton{}, err
	}
	return Skeleton{Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}, nil
}

func hasChartPayload(m *chartmodel.Chart) bool {
	switch m.Kind {
	case chartmodel.KindGantt:
		return m.Gantt != nil
	case chartmodel.KindRadar:
		return m.Radar != nil
	case chartmodel.KindTreemap:
		return m.Treemap != nil
	case chartmodel.KindPie:
		return m.Pie != nil
	case chartmodel.KindVenn:
		return m.Venn != nil
	case chartmodel.KindSankey:
		return m.Sankey != nil
	case chartmodel.KindXYChart:
		return m.XY != nil
	default:
		return false
	}
}

func constant(profile scene.Profile, name string) (int64, error) {
	key := profile.String() + "." + name
	for _, c := range gen.LayoutConst {
		if c.Name == key {
			return int64(c.Value), nil
		}
	}
	return 0, fmt.Errorf("chart layout: missing constant %s: %w", key, errDomain)
}

func i32(v int64) (int32, error) {
	if v < int64(-geom.I32Max) || v > int64(geom.I32Max) {
		return 0, ErrOverflow
	}
	return int32(v), nil
}

type rect struct{ x, y, w, h int64 }

func (r rect) geom() (geom.Rect, error) {
	var out geom.Rect
	var err error
	for _, field := range []struct {
		into *int32
		from int64
	}{{&out.X, r.x}, {&out.Y, r.y}, {&out.W, r.w}, {&out.H, r.h}} {
		if *field.into, err = i32(field.from); err != nil {
			return geom.Rect{}, err
		}
	}
	return out, nil
}
