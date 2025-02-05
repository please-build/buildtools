/*
Copyright 2016 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

// Tables about what Buildifier can and cannot edit.
// Perhaps eventually this will be
// derived from the BUILD encyclopedia.

package tables

// IsLabelArg: a named argument to a rule call is considered to have a value
// that can be treated as a label or list of labels if the name
// is one of these names. There is a separate denylist for
// rule-specific exceptions.
var IsLabelArg = map[string]bool{
	"app_target":         true,
	"appdir":             true,
	"base_package":       true,
	"build_deps":         true,
	"cc_deps":            true,
	"ccdeps":             true,
	"common_deps":        true,
	"compile_deps":       true,
	"compiler":           true,
	"data":               true,
	"default_visibility": true,
	"dep":                true,
	"deps":               true,
	"deps_java":          true,
	"dont_depend_on":     true,
	"env_deps":           true,
	"envscripts":         true,
	"exported_deps":      true,
	"exports":            true,
	"externs_list":       true,
	"files":              true,
	"globals":            true,
	"implementation":     true,
	"implements":         true,
	"includes":           true,
	"interface":          true,
	"jar":                true,
	"jars":               true,
	"javadeps":           true,
	"lib_deps":           true,
	"library":            true,
	"malloc":             true,
	"model":              true,
	"mods":               true,
	"module_deps":        true,
	"module_target":      true,
	"of":                 true,
	"plugins":            true,
	"proto_deps":         true,
	"proto_target":       true,
	"protos":             true,
	"resource":           true,
	"resources":          true,
	"runtime_deps":       true,
	"scope":              true,
	"shared_deps":        true,
	"similar_deps":       true,
	"source_jar":         true,
	"src":                true,
	"srcs":               true,
	"stripped_targets":   true,
	"suites":             true,
	"swigdeps":           true,
	"target":             true,
	"target_devices":     true,
	"target_platforms":   true,
	"template":           true,
	"test":               true,
	"tests":              true,
	"tests_deps":         true,
	"tool":               true,
	"tools":              true,
	"visibility":         true,
}

// LabelDenylist is the list of call arguments that cannot be
// shortened, because they are not interpreted using the same
// rules as for other labels.
var LabelDenylist = map[string]bool{
	// Shortening this can cause visibility checks to fail.
	"package_group.includes": true,
}

// By default, edit.types.IsList consults lang.TypeOf to determine if an arg is a list.
// You may override this using IsListArg. Specifying a name here overrides any value
// in lang.TypeOf.
var IsListArg = map[string]bool{}

// IsSortableListArg: a named argument to a rule call is considered to be a sortable list
// if the name is one of these names. There is a separate denylist for
// rule-specific exceptions.
var IsSortableListArg = map[string]bool{
	"cc_deps":             true,
	"common_deps":         true,
	"compile_deps":        true,
	"configs":             true,
	"constraints":         true,
	"data":                true,
	"default_visibility":  true,
	"deps":                true,
	"deps_java":           true,
	"exported_deps":       true,
	"exports":             true,
	"filegroups":          true,
	"files":               true,
	"hdrs":                true,
	"imports":             true,
	"includes":            true,
	"inherits":            true,
	"javadeps":            true,
	"lib_deps":            true,
	"module_deps":         true,
	"out":                 true,
	"outs":                true,
	"packages":            true,
	"plugin_modules":      true,
	"proto_deps":          true,
	"protos":              true,
	"pubs":                true,
	"resources":           true,
	"runtime_deps":        true,
	"shared_deps":         true,
	"similar_deps":        true,
	"srcs":                true,
	"swigdeps":            true,
	"swig_includes":       true,
	"tags":                true,
	"tests":               true,
	"tools":               true,
	"to_start_extensions": true,
	"visibility":          true,
}

// SortableDenylist records specific rule arguments that must not be reordered.
var SortableDenylist = map[string]bool{
	"genrule.outs":       true,
	"genrule.srcs":       true,
	"cc_embed_data.srcs": true,
}

// SortableAllowlist records specific rule arguments that are guaranteed to be reorderable
// (format: "rule_name.attribute_name").
var SortableAllowlist = map[string]bool{}

// NamePriority maps an argument name to its sorting priority.
//
// NOTE(bazel-team): These are the old buildifier rules. It is likely that this table
// will change, perhaps swapping in a separate table for each call,
// derived from the order used in the Build Encyclopedia.
var NamePriority = map[string]int{
	"name":              -99,
	"gwt_name":          -98,
	"package_name":      -97,
	"visible_node_name": -96, // for boq_initial_css_modules and boq_jswire_test_suite
	"build_rule.tag":    -95,
	"filegroup.tag":     -95,
	"size":              -94,
	"timeout":           -93,
	"testonly":          -92,
	"src":               -91,
	"srcdir":            -90,
	"srcs":              -89,
	"out":               -88,
	"outs":              -87,
	"hdrs":              -86,
	"has_services":      -85, // before api versions, for proto
	"include":           -84, // before exclude, for glob
	"of":                -83, // for check_dependencies
	"baseline":          -82, // for searchbox_library
	// All others sort here, at 0.
	"destdir":        1,
	"exports":        2,
	"runtime_deps":   3,
	"deps":           4,
	"implementation": 5,
	"implements":     6,
	"alwayslink":     7,
}

var StripLabelLeadingSlashes = false

var ShortenAbsoluteLabelsToRelative = false

// AndroidNativeRules lists all Android rules that are being migrated from Native to Starlark.
var AndroidNativeRules = []string{
	"aar_import",
	"android_binary",
	"android_device",
	"android_instrumentation_test",
	"android_library",
	"android_local_test",
	"android_ndk_respository",
	"android_sdk_repository",
}

// AndroidLoadPath is the load path for the Starlark Android Rules.
var AndroidLoadPath = "@rules_android//android:rules.bzl"

// CcNativeRules lists all C++ rules that are being migrated from Native to Starlark.
var CcNativeRules = []string{
	"cc_binary",
	"cc_test",
	"cc_library",
	"cc_import",
	"cc_proto_library",
	"fdo_prefetch_hints",
	"fdo_profile",
	"cc_toolchain",
	"cc_toolchain_suite",
	"objc_library",
	"objc_import",
}

// CcLoadPath is the load path for the Starlark C++ Rules.
var CcLoadPath = "@rules_cc//cc:defs.bzl"

// JavaNativeRules lists all Java rules that are being migrated from Native to Starlark.
var JavaNativeRules = []string{
	"java_binary",
	"java_import",
	"java_library",
	"java_lite_proto_library",
	"java_proto_library",
	"java_test",
	"java_package_configuration",
	"java_plugin",
	"java_runtime",
	"java_toolchain",
}

// JavaLoadPath is the load path for the Starlark Java Rules.
var JavaLoadPath = "@rules_java//java:defs.bzl"

// PyNativeRules lists all Python rules that are being migrated from Native to Starlark.
var PyNativeRules = []string{
	"py_library",
	"py_binary",
	"py_test",
	"py_runtime",
}

// PyLoadPath is the load path for the Starlark Python Rules.
var PyLoadPath = "@rules_python//python:defs.bzl"

// ProtoNativeRules lists all Proto rules that are being migrated from Native to Starlark.
var ProtoNativeRules = []string{
	"proto_lang_toolchain",
	"proto_library",
}

// ProtoNativeSymbols lists all Proto symbols that are being migrated from Native to Starlark.
var ProtoNativeSymbols = []string{
	"ProtoInfo",
	"proto_common",
}

// ProtoLoadPath is the load path for the Starlark Proto Rules.
var ProtoLoadPath = "@rules_proto//proto:defs.bzl"

// OverrideTables allows a user of the build package to override the special-case rules. The user-provided tables replace the built-in tables.
func OverrideTables(labelArg, denylist, listArg, sortableListArg, sortDenylist, sortAllowlist map[string]bool, namePriority map[string]int, stripLabelLeadingSlashes, shortenAbsoluteLabelsToRelative bool) {
	IsLabelArg = labelArg
	LabelDenylist = denylist
	IsListArg = listArg
	IsSortableListArg = sortableListArg
	SortableDenylist = sortDenylist
	SortableAllowlist = sortAllowlist
	NamePriority = namePriority
	StripLabelLeadingSlashes = stripLabelLeadingSlashes
	ShortenAbsoluteLabelsToRelative = shortenAbsoluteLabelsToRelative
}

// MergeTables allows a user of the build package to override the special-case rules. The user-provided tables are merged into the built-in tables.
func MergeTables(labelArg, denylist, listArg, sortableListArg, sortDenylist, sortAllowlist map[string]bool, namePriority map[string]int, stripLabelLeadingSlashes, shortenAbsoluteLabelsToRelative bool) {
	for k, v := range labelArg {
		IsLabelArg[k] = v
	}
	for k, v := range denylist {
		LabelDenylist[k] = v
	}
	for k, v := range listArg {
		IsListArg[k] = v
	}
	for k, v := range sortableListArg {
		IsSortableListArg[k] = v
	}
	for k, v := range sortDenylist {
		SortableDenylist[k] = v
	}
	for k, v := range sortAllowlist {
		SortableAllowlist[k] = v
	}
	for k, v := range namePriority {
		NamePriority[k] = v
	}
	StripLabelLeadingSlashes = stripLabelLeadingSlashes || StripLabelLeadingSlashes
	ShortenAbsoluteLabelsToRelative = shortenAbsoluteLabelsToRelative || ShortenAbsoluteLabelsToRelative
}
