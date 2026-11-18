package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type regionSet struct {
	parent  string
	regions []string
}

type regionMetadata struct {
	sets  []regionSet
	lineH int32
}

func groupBoxIDs(in Input) []string {
	var ids []string
	for _, b := range in.Boxes {
		if b.Role == scene.RoleGroup {
			ids = append(ids, b.ID)
		}
	}
	return ids
}

func validateRegionSets(in Input) error {
	if len(in.RegionSets) == 0 {
		return nil
	}
	parents, err := regionGroupParents(in)
	if err != nil {
		return err
	}
	sets := make([]localRegionSet, len(in.RegionSets))
	for i, set := range in.RegionSets {
		sets[i] = localRegionSet{parent: set.Parent, regions: set.Regions}
	}
	indexed, err := indexGroups(parents, sets)
	if err != nil {
		return err
	}
	depths := make([]int, len(parents))
	for _, parent := range indexed.order {
		for _, child := range indexed.children[parent] {
			depths[child] = depths[parent] + 1
			if depths[child] >= 64 {
				return ErrGraph
			}
		}
	}
	return nil
}

func groupIndexByID(in Input) (map[string]int, error) {
	groups := make(map[string]int)
	for i, id := range groupBoxIDs(in) {
		if _, ok := groups[id]; ok || id == "" {
			return nil, ErrGraph
		}
		groups[id] = i
	}
	return groups, nil
}

func regionGroupParents(in Input) ([]int, error) {
	groups, err := groupIndexByID(in)
	if err != nil {
		return nil, err
	}
	boxes := make(map[string]struct{}, len(in.Boxes))
	parents := make([]int, 0, len(groups))
	for _, b := range in.Boxes {
		if _, ok := boxes[b.ID]; ok || b.ID == "" {
			return nil, ErrGraph
		}
		boxes[b.ID] = struct{}{}
		parent, ok := groups[b.Parent]
		if !ok && b.Parent != "" {
			return nil, ErrGraph
		}
		if !ok {
			parent = -1
		}
		if b.Role == scene.RoleGroup {
			parents = append(parents, parent)
		}
	}
	return parents, nil
}

func regionMember(in Input, id string) bool {
	groups := groupBoxIDs(in)
	for _, set := range in.RegionSets {
		for _, region := range set.Regions {
			if group, err := groupAt(groups, region); err == nil && group == id {
				return true
			}
		}
	}
	return false
}

func ownsRegions(in Input, id string) bool {
	groups := groupBoxIDs(in)
	for _, set := range in.RegionSets {
		if group, err := groupAt(groups, set.Parent); err == nil && group == id {
			return true
		}
	}
	return false
}

func collapsedRegionSets(in Input, id string, out Input) ([]RegionSet, error) {
	return projectRegionSets(in, func(group string) bool { return group != id && hasInputBox(out, group) }, out)
}

func subgraphRegionSets(in Input, sub Input) ([]RegionSet, error) {
	return projectRegionSets(in, func(group string) bool { return hasInputBox(sub, group) }, sub)
}

func groupAt(groups []string, index int) (string, error) {
	if index < 0 || index >= len(groups) {
		return "", ErrGraph
	}
	return groups[index], nil
}

func projectRegionSets(in Input, retained func(string) bool, out Input) ([]RegionSet, error) {
	before, after := groupBoxIDs(in), groupBoxIDs(out)
	var sets []RegionSet
	for _, set := range in.RegionSets {
		ids, err := regionSetIDs(before, set)
		if err != nil {
			return nil, err
		}
		if !retained(ids.parent) {
			continue
		}
		projected := RegionSet{Parent: slices.Index(after, ids.parent), Regions: make([]int, len(ids.regions))}
		for i, region := range ids.regions {
			projected.Regions[i] = slices.Index(after, region)
			if !retained(region) || projected.Regions[i] < 0 {
				return nil, ErrGraph
			}
		}
		if projected.Parent < 0 {
			return nil, ErrGraph
		}
		sets = append(sets, projected)
	}
	return sets, nil
}

func regionSetIDs(groups []string, set RegionSet) (regionSet, error) {
	parent, err := groupAt(groups, set.Parent)
	if err != nil {
		return regionSet{}, err
	}
	ids := regionSet{parent: parent, regions: make([]string, len(set.Regions))}
	for i, region := range set.Regions {
		if ids.regions[i], err = groupAt(groups, region); err != nil {
			return regionSet{}, err
		}
	}
	return ids, nil
}

func graphRegions(in Input, profile scene.Profile) (regionMetadata, error) {
	if len(in.RegionSets) == 0 {
		return regionMetadata{}, nil
	}
	groups := groupBoxIDs(in)
	metadata := regionMetadata{sets: make([]regionSet, len(in.RegionSets)), lineH: constant(profile, "line_h")}
	for i, set := range in.RegionSets {
		ids, err := regionSetIDs(groups, set)
		if err != nil {
			return regionMetadata{}, err
		}
		metadata.sets[i] = ids
	}
	return metadata, nil
}

func stripRegionRoot(s *scene.Scene, id string) {
	s.Boxes = slices.DeleteFunc(s.Boxes, func(b scene.Box) bool { return b.ID == id })
	s.Groups = slices.DeleteFunc(s.Groups, func(g *scene.Group) bool { return g.Owner == id })
}
