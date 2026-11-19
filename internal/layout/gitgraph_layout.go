package layout

import (
	"errors"
	"fmt"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/lanes"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var errGitgraphInput = errors.New("gitgraph layout: endpoint is not a commit")

type labelSlot struct {
	branch, commit, tag int
}

type decodedGitgraph struct {
	graph lanes.GitGraphInput
	slots []labelSlot
}

func layoutGitgraph(in Input) (scene.Scene, []diag.Diagnostic, error) {
	decoded, err := decodeGitgraph(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	res, err := lanes.GitGraph(decoded.graph, lanes.Params{Profile: in.Profile})
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: decoded.dump(in, res), Groups: res.Groups}, nil, nil
}

func laneOrder(shape string) (int64, bool) {
	order, found := strings.CutPrefix(shape, branchShape+":")
	if !found {
		return 0, false
	}
	value, err := strconv.ParseInt(order, 10, 64)
	return value, err == nil
}

func commitKind(shape string) string {
	if shape == "" {
		return "commit"
	}
	return shape
}

func decodeGitgraph(in Input) (decodedGitgraph, error) {
	d := decodedGitgraph{graph: lanes.GitGraphInput{
		Direction:    in.Direction,
		ShowBranches: configFlag(in.Options.Config, showBranches, true),
		RotateLabels: configFlag(in.Options.Config, rotateLabels, true),
	}}
	laneAt, commitAt := map[string]int{}, map[string]int{}
	for _, box := range in.Boxes {
		if box.Role == scene.RoleGroup {
			order, has := laneOrder(box.Shape)
			laneAt[box.ID] = len(d.graph.Branches)
			d.graph.Branches = append(d.graph.Branches, lanes.Branch{ID: box.ID, Order: order, HasOrder: has})
			continue
		}
		lane, known := laneAt[box.Parent]
		if !known {
			lane = len(d.graph.Branches)
			laneAt[box.Parent] = lane
			d.graph.Branches = append(d.graph.Branches, lanes.Branch{ID: box.Parent})
		}
		commitAt[box.ID] = len(d.graph.Commits)
		d.graph.Commits = append(d.graph.Commits, lanes.Commit{ID: box.ID, Branch: lane, Kind: commitKind(box.Shape)})
	}
	for _, route := range in.Routes {
		from, fromKnown := commitAt[route.From]
		to, toKnown := commitAt[route.To]
		if !fromKnown || !toKnown {
			return d, fmt.Errorf("route %q: %w", route.ID, errGitgraphInput)
		}
		d.graph.Links = append(d.graph.Links, lanes.Link{ID: route.ID, From: from, To: to, Pick: route.Line == "dotted"})
	}
	return d, d.attach(in, laneAt, commitAt)
}

func (d *decodedGitgraph) attach(in Input, laneAt, commitAt map[string]int) error {
	commitLabels := configFlag(in.Options.Config, showCommitIDs, true)
	for _, label := range in.Labels {
		text, err := measureGitgraphText(in.Profile, label)
		if err != nil {
			return err
		}
		if lane, isLane := laneAt[label.Owner]; isLane {
			d.graph.Branches[lane].Label = &text
			d.slots = append(d.slots, labelSlot{branch: lane, commit: -1, tag: -1})
			continue
		}
		at, isCommit := commitAt[label.Owner]
		if !isCommit {
			return fmt.Errorf("label %q: %w", label.ID, errGitgraphInput)
		}
		commit := &d.graph.Commits[at]
		if commitLabels && commit.Label == nil {
			commit.Label = &text
			d.slots = append(d.slots, labelSlot{branch: -1, commit: at, tag: -1})
			continue
		}
		d.slots = append(d.slots, labelSlot{branch: -1, commit: at, tag: len(commit.Tags)})
		commit.Tags = append(commit.Tags, text)
	}
	return nil
}

func measureGitgraphText(profile scene.Profile, label Label) (lanes.Text, error) {
	lineHeight, ok := layoutConstant(profile, "line_h")
	if !ok {
		return lanes.Text{}, lanes.ErrConstants
	}
	metric := measure.CellMetric()
	if profile == scene.ProfileVector {
		metric = measure.ForRole(measureRole(label.Role))
	}
	lines, err := measure.StyledLines(label.Text, geom.I32Max, metric)
	if err != nil {
		return lanes.Text{}, geom.ErrOverflow
	}
	var widest int32
	for _, line := range lines {
		widest = max(widest, line.Width)
	}
	return lanes.Text{Lines: lines, W: widest, H: int32(len(lines)) * lineHeight, Role: label.Role}, nil
}

func measureRole(role scene.TextRole) measure.Role {
	if role == scene.TextRoleBody {
		return measure.RoleBody
	}
	return measure.RoleLabel
}

func (d *decodedGitgraph) dump(in Input, res lanes.GitGraphResult) scene.Dump {
	options := in.Options
	options.Profile, options.Direction = in.Profile, in.Direction
	dump := scene.Dump{Stage: scene.StageLayout, Kind: gitgraphKind, Options: options, Canvas: res.Canvas}
	lane, commit := 0, 0
	for _, box := range in.Boxes {
		var rect geom.Rect
		if box.Role == scene.RoleGroup {
			rect, lane = res.Lanes[lane], lane+1
		} else {
			rect, commit = geom.Rect{X: res.Points[commit].X, Y: res.Points[commit].Y}, commit+1
		}
		dump.Boxes = append(dump.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: rect, Parent: box.Parent, Exclusive: box.Exclusive, Shape: box.Shape, Text: box.Text})
	}
	for i, route := range in.Routes {
		dump.Routes = append(dump.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: route.Orthogonal, Points: res.Routes[i], Stroke: route.Line})
	}
	for i, label := range in.Labels {
		rect, text := d.labelGeometry(d.slots[i], res)
		lines := make([]string, len(text.Lines))
		for k, line := range text.Lines {
			lines[k] = line.Text
		}
		dump.Labels = append(dump.Labels, scene.Label{ID: label.ID, Owner: label.Owner, Text: label.Text, Rect: rect, Lines: lines})
	}
	return dump
}

func (d *decodedGitgraph) labelGeometry(slot labelSlot, res lanes.GitGraphResult) (geom.Rect, lanes.Text) {
	switch {
	case slot.branch >= 0:
		return res.BranchLabels[slot.branch], *d.graph.Branches[slot.branch].Label
	case slot.tag < 0:
		return res.CommitLabels[slot.commit], *d.graph.Commits[slot.commit].Label
	}
	return res.TagLabels[slot.commit][slot.tag], d.graph.Commits[slot.commit].Tags[slot.tag]
}
