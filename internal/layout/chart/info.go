package chart

import (
	"context"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	infoKind    = "info"
	infoBoxID   = "info"
	infoLabelID = "version"
)

type InfoFrame struct {
	Box   scene.Box
	Label scene.Label
}

func InfoSkeleton(m *chartmodel.Info) InfoFrame {
	return InfoFrame{
		Box:   scene.Box{ID: infoBoxID, Role: scene.RoleNode},
		Label: scene.Label{ID: infoLabelID, Owner: infoBoxID, Text: m.Text},
	}
}

type infoConsts struct {
	width, height, textX, textY, fontSize int64
}

func loadInfoConsts(profile scene.Profile) (infoConsts, error) {
	var c infoConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"info.width", &c.width}, {"info.height", &c.height}, {"info.text_x", &c.textX},
		{"info.text_y", &c.textY}, {"info.font_size", &c.fontSize},
	} {
		value, err := constant(profile, row.name)
		if err != nil {
			return infoConsts{}, err
		}
		*row.into = value
	}
	return c, nil
}

type infoPlan struct {
	style  textStyle
	box    textBox
	at     rect
	canvas rect
}

func LayoutInfo(ctx context.Context, m *chartmodel.Info, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	if err := ctx.Err(); err != nil {
		return scene.Scene{}, nil, err
	}
	c, err := loadInfoConsts(o.Profile)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	style := textStyle{profile: o.Profile, role: measure.RoleTitle, size: int32(c.fontSize / 64)}
	box, err := style.measure(m.Text)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	at := rect{c.textX - geom.FloorDiv(box.w, 2), c.textY - geom.FloorDiv(box.h, 2), box.w, box.h}
	at.x, at.y = max(at.x, 0), max(at.y, 0)
	canvas := rect{0, 0, max(c.width, at.right()), max(c.height, at.bottom())}
	return infoPlan{style: style, box: box, at: at, canvas: canvas}.scene(m, o)
}

func (p infoPlan) scene(m *chartmodel.Info, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	frame := InfoSkeleton(m)
	var err error
	if frame.Box.Rect, err = p.canvas.geom(); err != nil {
		return scene.Scene{}, nil, err
	}
	if frame.Label.Rect, err = p.at.geom(); err != nil {
		return scene.Scene{}, nil, err
	}
	frame.Label.Lines = p.box.plain()
	text, err := p.style.item(p.box, p.at, scene.AlignMiddle)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: infoKind, Options: o, Canvas: geom.Size{W: frame.Box.Rect.W, H: frame.Box.Rect.H}}
	dump.Options.Direction = scene.DirectionTB
	dump.Boxes, dump.Labels = []scene.Box{frame.Box}, []scene.Label{frame.Label}
	return scene.Scene{Dump: dump, Groups: []*scene.Group{{Role: scene.GroupRoleNode, Owner: infoBoxID, Items: []scene.Primitive{text}}}}, nil, nil
}
