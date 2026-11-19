package layout

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	gitmodel "github.com/gosuda/elegant-mermaid/internal/model/gitgraph"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	gitgraphKind  = "gitgraph"
	branchShape   = "branch"
	showBranches  = "showBranches"
	showCommitIDs = "showCommitLabel"
	rotateLabels  = "rotateCommitLabel"
)

func FromGitgraph(m *gitmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	for _, entry := range m.Config {
		options.Config = append(options.Config, scene.ConfigBool(entry.Key, entry.Value))
	}
	options.Profile = profile
	author := &gitgraphAuthor{
		model:    m,
		in:       Input{Kind: gitgraphKind, Profile: profile, Direction: gitgraphDirection(m.Direction), Options: options},
		used:     map[string]struct{}{},
		commitAt: map[string]int{},
	}
	author.lanes()
	author.commits()
	author.links()
	author.labels()
	return author.in, nil
}

func gitgraphDirection(name string) scene.Direction {
	switch name {
	case "LR":
		return scene.DirectionLR
	case "TB":
		return scene.DirectionTB
	case "BT":
		return scene.DirectionBT
	}
	return scene.DirectionRL
}

func configFlag(config []scene.Config, key string, fallback bool) bool {
	i := slices.IndexFunc(config, func(c scene.Config) bool { return c.Key == key })
	if i < 0 {
		return fallback
	}
	return config[i].Value == "true"
}

type gitgraphAuthor struct {
	model     *gitmodel.Model
	in        Input
	used      map[string]struct{}
	laneIDs   []string
	commitIDs []string
	commitAt  map[string]int
}

func (a *gitgraphAuthor) unique(wanted string) string {
	candidate := wanted
	for ordinal := 1; ; ordinal++ {
		if _, taken := a.used[candidate]; !taken {
			a.used[candidate] = struct{}{}
			return candidate
		}
		candidate = wanted + "~" + strconv.Itoa(ordinal)
	}
}

func (a *gitgraphAuthor) lanes() {
	for index, branch := range a.model.Branches {
		id := a.unique("lane" + strconv.Itoa(index))
		a.laneIDs = append(a.laneIDs, id)
		shape := branchShape
		if branch.HasOrder {
			shape += ":" + strconv.FormatInt(branch.Order, 10)
		}
		a.in.Boxes = append(a.in.Boxes, Box{ID: id, Role: scene.RoleGroup, Shape: shape, Text: branch.Name})
	}
}

func commitShape(c gitmodel.Commit) string {
	if c.Kind == gitmodel.KindCherryPick {
		return "cherry-pick"
	}
	base := "commit"
	if c.Kind == gitmodel.KindMerge {
		base = "merge"
	}
	switch c.Type {
	case gitmodel.TypeReverse:
		return commitVariant(base, "reverse")
	case gitmodel.TypeHighlight:
		return commitVariant(base, "highlight")
	}
	return base
}

func commitVariant(base, variant string) string {
	if base == "commit" {
		return variant
	}
	return base + "-" + variant
}

func (a *gitgraphAuthor) commits() {
	for index, commit := range a.model.Commits {
		id := a.unique(commit.ID)
		a.commitIDs = append(a.commitIDs, id)
		a.commitAt[commit.ID] = index
		a.in.Boxes = append(a.in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: commitShape(commit), Parent: a.laneIDs[commit.Branch], Exclusive: true, Text: id})
	}
}

func (a *gitgraphAuthor) links() {
	for to, commit := range a.model.Commits {
		for _, parent := range commit.Parents {
			if from, ok := a.commitAt[parent]; ok && from < to {
				a.link(from, to, "normal")
			}
		}
		if from, ok := a.commitAt[commit.Pick]; ok && commit.Pick != "" && from != to {
			a.link(from, to, "dotted")
		}
	}
}

func (a *gitgraphAuthor) link(from, to int, line string) {
	id := a.unique("e" + strconv.Itoa(len(a.in.Routes)))
	a.in.Routes = append(a.in.Routes, Route{ID: id, From: a.commitIDs[from], To: a.commitIDs[to], Orthogonal: true, Line: line})
}

func (a *gitgraphAuthor) labels() {
	if configFlag(a.in.Options.Config, showBranches, true) {
		for index, branch := range a.model.Branches {
			a.label(a.laneIDs[index], ".label", scene.TextRoleLabel, branch.Name)
		}
	}
	commitLabels := configFlag(a.in.Options.Config, showCommitIDs, true)
	for index, commit := range a.model.Commits {
		if commitLabels {
			a.label(a.commitIDs[index], ".label", scene.TextRoleBody, commit.ID)
		}
		for k, tag := range commit.Tags {
			a.label(a.commitIDs[index], ".tag"+strconv.Itoa(k), scene.TextRoleBody, tag)
		}
	}
}

func (a *gitgraphAuthor) label(owner, suffix string, role scene.TextRole, text string) {
	a.in.Labels = append(a.in.Labels, Label{ID: a.unique(owner + suffix), Owner: owner, Role: role, Text: text})
}
