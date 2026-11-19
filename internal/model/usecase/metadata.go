package usecase

import (
	"fmt"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
)

func invalidMetadata(key, kind, id string, span source.Span) diag.Diagnostic {
	return issue("usecase/invalid-metadata", fmt.Sprintf("invalid metadata %s for %s %s", key, kind, id), span)
}

func isBoolean(token syn.Token) bool { return token.Kind == "TRUE" || token.Kind == "FALSE" }

func applyMetadata(node *Node, metadata *syn.Metadata, ds *[]diag.Diagnostic) {
	if metadata == nil {
		return
	}
	if node.Kind == KindJSON && len(metadata.Properties) == 0 {
		*ds = append(*ds, invalidMetadata("metadata", KindJSON.String(), node.ID, metadata.Span))
		return
	}
	for i := range metadata.Properties {
		property := &metadata.Properties[i]
		key, value := content(property.Key), content(property.Value)
		if !setMetadata(node, key, value, property.Value) {
			*ds = append(*ds, invalidMetadata(key, node.Kind.String(), node.ID, property.Span))
			continue
		}
		if j := slices.IndexFunc(node.Metadata, func(f Field) bool { return f.Key == key }); j >= 0 {
			node.Metadata[j].Value = value
		} else {
			node.Metadata = append(node.Metadata, Field{Key: key, Value: value})
		}
	}
}

var actorTypes = []string{"normal", "hollow", "awesome"}

func setMetadata(node *Node, key, value string, token syn.Token) bool {
	switch node.Kind {
	case KindActor:
		return setActorMetadata(node, key, value, token)
	case KindUsecase:
		return setBusiness(node, key, value, token)
	case KindBoundary:
		return setBoundaryType(node, key, value)
	}
	return false
}

func setActorMetadata(node *Node, key, value string, token syn.Token) bool {
	switch {
	case key == "type" && slices.Contains(actorTypes, value):
		node.ActorType = value
	case key == "icon" && !isBoolean(token):
		node.Icon = value
	default:
		return setBusiness(node, key, value, token)
	}
	return true
}

func setBusiness(node *Node, key, value string, token syn.Token) bool {
	if key != "business" || !isBoolean(token) {
		return false
	}
	node.Business = value == "true"
	return true
}

func setBoundaryType(node *Node, key, value string) bool {
	if key != "type" || (value != "rect" && value != "package") {
		return false
	}
	node.BoundaryType = value
	return true
}

func applyEdgeMetadata(edge *Relation, property *syn.MetadataProperty, ds *[]diag.Diagnostic) {
	key, value := content(property.Key), content(property.Value)
	switch {
	case key == "animate" && isBoolean(property.Value):
		edge.Animate = value == "true"
	case key == "animation" && (value == "fast" || value == "slow"):
		edge.Animation, edge.Animate = value, true
	default:
		*ds = append(*ds, invalidMetadata(key, "edge", edge.ID, property.Span))
	}
}

func validateNode(node *Node, ds *[]diag.Diagnostic) {
	if node.Kind == KindUsecase && node.Shape == "rect" && node.Business {
		*ds = append(*ds, issue("usecase/invalid-business-usecase", fmt.Sprintf("rectangular use case %s cannot be business", node.ID), node.Span))
	}
	if node.Kind != KindActor {
		return
	}
	var reason string
	switch {
	case node.Icon != "" && node.ActorType != "normal":
		reason = "icon cannot combine with hollow or awesome type"
	case node.Business && node.ActorType == "awesome":
		reason = "business actor must use normal or hollow geometry"
	default:
		return
	}
	*ds = append(*ds, issue("usecase/invalid-actor", fmt.Sprintf("invalid actor %s: %s", node.ID, reason), node.Span))
}

func applyArrow(edge *Relation, arrow *syn.Arrow) {
	switch {
	case arrow.Semantic != nil:
		applySemantic(edge, arrow.Semantic)
	case arrow.ForwardSolid != nil:
		applySolid(edge, arrow.ForwardSolid.Token.Text, "point")
	case arrow.BackwardSolid != nil:
		applyBackwardSolid(edge, arrow.BackwardSolid)
	case arrow.MarkerlessSolid != nil:
		applyMarkerlessSolid(edge, arrow.MarkerlessSolid)
	case arrow.ForwardCircle != nil:
		edge.MarkerEnd = "circle"
	case arrow.ForwardCross != nil:
		edge.MarkerEnd = "cross"
	case arrow.BackwardCircle != nil:
		edge.MarkerStart = "circle"
		edge.Label = edgeLabel(arrow.BackwardCircle.Label)
	case arrow.BackwardCross != nil:
		edge.MarkerStart = "cross"
		edge.Label = edgeLabel(arrow.BackwardCross.Label)
	}
}

func applyBackwardSolid(edge *Relation, op *syn.BackwardSolidOperator) {
	edge.MarkerStart = "point"
	applySolid(edge, op.Token.Text, "none")
	if op.Right != nil {
		edge.MinLength = max(edge.MinLength, solidMinLength(op.Right.Text))
	}
	edge.Label = edgeLabel(op.Label)
}

func applyMarkerlessSolid(edge *Relation, op *syn.MarkerlessSolidOperator) {
	right := op.Token.Text
	if op.Right != nil {
		right = op.Right.Text
	}
	applySolid(edge, right, associationMarker(right))
	edge.Label = edgeLabel(op.Label)
}

func applySemantic(edge *Relation, relation *syn.SemanticRelation) {
	if relation.Relation == nil {
		edge.Kind, edge.MarkerEnd = "generalization", "extension"
		return
	}
	edge.Kind = strings.ToLower(relation.Relation.Text)
	edge.Label = "«" + edge.Kind + "»"
	edge.MarkerEnd = "point"
}

func associationMarker(operator string) string {
	switch operator[len(operator)-1] {
	case '>':
		return "point"
	case 'o':
		return "circle"
	case 'x':
		return "cross"
	}
	return "none"
}

func applySolid(edge *Relation, operator, marker string) {
	edge.MarkerEnd = marker
	edge.MinLength = solidMinLength(operator)
	if marker == "circle" || marker == "cross" {
		edge.MinLength = 1
	}
}

func solidMinLength(operator string) int {
	return max(strings.Count(operator, "-")-1, 1)
}

func edgeLabel(label *syn.EdgeLabel) string {
	if label == nil {
		return ""
	}
	return label.Label.Text
}
