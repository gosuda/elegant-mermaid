package c4

const macroMode = "macro"

func isMacroKind(kind string) bool {
	switch kind {
	case "PERSON", "PERSON_EXT",
		"SYSTEM", "SYSTEM_DB", "SYSTEM_QUEUE", "SYSTEM_EXT", "SYSTEM_EXT_DB", "SYSTEM_EXT_QUEUE",
		"CONTAINER", "CONTAINER_DB", "CONTAINER_QUEUE", "CONTAINER_EXT", "CONTAINER_EXT_DB", "CONTAINER_EXT_QUEUE",
		"COMPONENT", "COMPONENT_DB", "COMPONENT_QUEUE", "COMPONENT_EXT", "COMPONENT_EXT_DB", "COMPONENT_EXT_QUEUE",
		"BOUNDARY", "ENTERPRISE_BOUNDARY", "SYSTEM_BOUNDARY", "CONTAINER_BOUNDARY",
		"NODE", "NODE_L", "NODE_R",
		"REL", "BIREL", "REL_U", "REL_D", "REL_L", "REL_R", "REL_B", "REL_INDEX",
		"UPDATE_EL_STYLE", "UPDATE_REL_STYLE", "UPDATE_LAYOUT_CONFIG":
		return true
	}
	return false
}

func isBoundaryKind(kind string) bool {
	switch kind {
	case "BOUNDARY", "ENTERPRISE_BOUNDARY", "SYSTEM_BOUNDARY", "CONTAINER_BOUNDARY", "NODE", "NODE_L", "NODE_R":
		return true
	}
	return false
}

func macroKind(name []byte) (string, bool) {
	kind := ""
	switch {
	case string(name) == "Boundary", hasSuffix(name, "_Boundary"):
		kind = boundaryKind(name)
	case hasPrefix(name, "System"):
		kind = systemKind(name)
	case hasPrefix(name, "Container"):
		kind = containerKind(name)
	case hasPrefix(name, "Component"):
		kind = componentKind(name)
	case hasPrefix(name, "Person"):
		kind = personKind(name)
	case hasPrefix(name, "Node"), string(name) == "Deployment_Node":
		kind = nodeKind(name)
	case hasPrefix(name, "Rel"), hasPrefix(name, "BiRel"):
		kind = relationKind(name)
	case hasPrefix(name, "Update"):
		kind = updateKind(name)
	}
	return kind, kind != ""
}

func boundaryKind(name []byte) string {
	switch string(name) {
	case "Boundary":
		return "BOUNDARY"
	case "Enterprise_Boundary":
		return "ENTERPRISE_BOUNDARY"
	case "System_Boundary":
		return "SYSTEM_BOUNDARY"
	case "Container_Boundary":
		return "CONTAINER_BOUNDARY"
	}
	return ""
}

func systemKind(name []byte) string {
	switch string(name) {
	case "System":
		return "SYSTEM"
	case "SystemDb":
		return "SYSTEM_DB"
	case "SystemQueue":
		return "SYSTEM_QUEUE"
	case "System_Ext":
		return "SYSTEM_EXT"
	case "SystemDb_Ext":
		return "SYSTEM_EXT_DB"
	case "SystemQueue_Ext":
		return "SYSTEM_EXT_QUEUE"
	}
	return ""
}

func containerKind(name []byte) string {
	switch string(name) {
	case "Container":
		return "CONTAINER"
	case "ContainerDb":
		return "CONTAINER_DB"
	case "ContainerQueue":
		return "CONTAINER_QUEUE"
	case "Container_Ext":
		return "CONTAINER_EXT"
	case "ContainerDb_Ext":
		return "CONTAINER_EXT_DB"
	case "ContainerQueue_Ext":
		return "CONTAINER_EXT_QUEUE"
	}
	return ""
}

func componentKind(name []byte) string {
	switch string(name) {
	case "Component":
		return "COMPONENT"
	case "ComponentDb":
		return "COMPONENT_DB"
	case "ComponentQueue":
		return "COMPONENT_QUEUE"
	case "Component_Ext":
		return "COMPONENT_EXT"
	case "ComponentDb_Ext":
		return "COMPONENT_EXT_DB"
	case "ComponentQueue_Ext":
		return "COMPONENT_EXT_QUEUE"
	}
	return ""
}

func personKind(name []byte) string {
	switch string(name) {
	case "Person":
		return "PERSON"
	case "Person_Ext":
		return "PERSON_EXT"
	}
	return ""
}

func nodeKind(name []byte) string {
	switch string(name) {
	case "Node", "Deployment_Node":
		return "NODE"
	case "Node_L":
		return "NODE_L"
	case "Node_R":
		return "NODE_R"
	}
	return ""
}

func relationKind(name []byte) string {
	switch string(name) {
	case "Rel":
		return "REL"
	case "BiRel":
		return "BIREL"
	case "Rel_Up", "Rel_U":
		return "REL_U"
	case "Rel_Down", "Rel_D":
		return "REL_D"
	case "Rel_Left", "Rel_L":
		return "REL_L"
	case "Rel_Right", "Rel_R":
		return "REL_R"
	case "Rel_Back":
		return "REL_B"
	case "RelIndex":
		return "REL_INDEX"
	}
	return ""
}

func updateKind(name []byte) string {
	switch string(name) {
	case "UpdateElementStyle":
		return "UPDATE_EL_STYLE"
	case "UpdateRelStyle":
		return "UPDATE_REL_STYLE"
	case "UpdateLayoutConfig":
		return "UPDATE_LAYOUT_CONFIG"
	}
	return ""
}

func headerKind(b []byte) (string, int) {
	switch {
	case hasPrefix(b, "C4Context"):
		return "C4_CONTEXT", len("C4Context")
	case hasPrefix(b, "C4Container"):
		return "C4_CONTAINER", len("C4Container")
	case hasPrefix(b, "C4Component"):
		return "C4_COMPONENT", len("C4Component")
	case hasPrefix(b, "C4Dynamic"):
		return "C4_DYNAMIC", len("C4Dynamic")
	case hasPrefix(b, "C4Deployment"):
		return "C4_DEPLOYMENT", len("C4Deployment")
	}
	return "", 0
}

func hasPrefix(b []byte, prefix string) bool {
	return len(b) >= len(prefix) && string(b[:len(prefix)]) == prefix
}

func hasSuffix(b []byte, suffix string) bool {
	return len(b) >= len(suffix) && string(b[len(b)-len(suffix):]) == suffix
}
