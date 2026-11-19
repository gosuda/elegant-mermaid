package chart

import (
	"slices"
	"strconv"
	"strings"

	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	cynefinKind    = "cynefin"
	cynefinFrameID = "frame"
	cynefinTitleID = "title"
	confusionName  = "confusion"
)

var cynefinOrder = [...]string{"complex", "complicated", "clear", "chaotic", "confusion"}

type CynefinFrame struct {
	Boxes  []scene.Box
	Routes []scene.Route
	Labels []scene.Label
}

type cynefinRoute struct {
	id, from, to, label string
}

func domainTitle(name string) string {
	return strings.ToUpper(name[:1]) + name[1:]
}

func domainLabelID(name string) string { return name + ".label" }

func itemLabelID(name string, index int) string { return name + ".i" + strconv.Itoa(index) }

func routeID(index int) string { return "e" + strconv.Itoa(index) }

func routeLabelID(index int) string { return routeID(index) + ".label" }

func normalizedDomains(c *chartmodel.Cynefin) []chartmodel.CynefinDomain {
	var out []chartmodel.CynefinDomain
	for _, d := range c.Domains {
		if slices.Contains(cynefinOrder[:], d.Name) && !slices.ContainsFunc(out, func(o chartmodel.CynefinDomain) bool { return o.Name == d.Name }) {
			out = append(out, d)
		}
	}
	for _, name := range cynefinOrder {
		if !slices.ContainsFunc(out, func(o chartmodel.CynefinDomain) bool { return o.Name == name }) {
			out = append(out, chartmodel.CynefinDomain{Name: name})
		}
	}
	return out
}

func cynefinRoutes(c *chartmodel.Cynefin) []cynefinRoute {
	var out []cynefinRoute
	for _, t := range c.Transitions {
		if t.From == t.To || !slices.Contains(cynefinOrder[:], t.From) || !slices.Contains(cynefinOrder[:], t.To) {
			continue
		}
		out = append(out, cynefinRoute{id: routeID(len(out)), from: t.From, to: t.To, label: t.Label})
	}
	return out
}

func CynefinSkeleton(c *chartmodel.Cynefin) CynefinFrame {
	frame := CynefinFrame{Boxes: []scene.Box{{ID: cynefinFrameID, Role: scene.RoleNode}}}
	if c.Title != "" {
		frame.Labels = append(frame.Labels, scene.Label{ID: cynefinTitleID, Owner: cynefinFrameID, Text: c.Title})
	}
	domains := normalizedDomains(c)
	for _, d := range domains {
		frame.Boxes = append(frame.Boxes, scene.Box{ID: d.Name, Role: scene.RoleNode, Parent: cynefinFrameID})
		frame.Labels = append(frame.Labels, scene.Label{ID: domainLabelID(d.Name), Owner: d.Name, Text: domainTitle(d.Name)})
		for i, item := range d.Items {
			frame.Labels = append(frame.Labels, scene.Label{ID: itemLabelID(d.Name, i), Owner: d.Name, Text: item})
		}
	}
	for i, r := range cynefinRoutes(c) {
		frame.Routes = append(frame.Routes, scene.Route{ID: r.id, From: r.from, To: r.to, Orthogonal: true})
		if r.label != "" {
			frame.Labels = append(frame.Labels, scene.Label{ID: routeLabelID(i), Owner: r.id, Text: r.label})
		}
	}
	return frame
}
