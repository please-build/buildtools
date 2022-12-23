/*
Copyright 2020 Google LLC

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

// Cosmetic warnings (e.g. for improved readability of Starlark files)

package warn

import (
	"regexp"
	"sort"
	"strings"

	"github.com/bazelbuild/buildtools/build"
	"github.com/bazelbuild/buildtools/edit"
)

func packageOnTopWarning(f *build.File) []*LinterFinding {
	seenRule := false
	for _, stmt := range f.Stmt {
		_, isString := stmt.(*build.StringExpr) // typically a docstring
		_, isComment := stmt.(*build.CommentBlock)
		_, isAssignExpr := stmt.(*build.AssignExpr) // e.g. variable declaration
		_, isPackageGroup := edit.ExprToRule(stmt, "package_group")
		_, isLicense := edit.ExprToRule(stmt, "licenses")
		if isString || isComment || isAssignExpr || isPackageGroup || isLicense || stmt == nil {
			continue
		}
		if rule, ok := edit.ExprToRule(stmt, "package"); ok {
			if !seenRule { // OK: package is on top of the file
				return nil
			}
			return []*LinterFinding{makeLinterFinding(rule.Call,
				"Package declaration should be at the top of the file, after the load() statements, "+
					"but before any call to a rule or a macro. "+
					"package_group() and licenses() may be called before package().")}
		}
		seenRule = true
	}
	return nil
}

// compareLoadLabels compares two module names
// If one label has explicit repository path (starts with @), it goes first
// If the packages are different, labels are sorted by package name (empty package goes first)
// If the packages are the same, labels are sorted by their name
func compareLoadLabels(load1Label, load2Label string) bool {
	// handle absolute labels with explicit repositories separately to
	// make sure they precede absolute and relative labels without repos
	isExplicitRepo1 := strings.HasPrefix(load1Label, "@")
	isExplicitRepo2 := strings.HasPrefix(load2Label, "@")

	if isExplicitRepo1 != isExplicitRepo2 {
		// Exactly one label has an explicit repository name, it should be the first one.
		return isExplicitRepo1
	}

	// Either both labels have explicit repository names or both don't, compare their packages
	// and break ties using file names if necessary
	module1Parts := strings.SplitN(load1Label, ":", 2)
	package1, filename1 := "", module1Parts[0]
	if len(module1Parts) == 2 {
		package1, filename1 = module1Parts[0], module1Parts[1]
	}
	module2Parts := strings.SplitN(load2Label, ":", 2)
	package2, filename2 := "", module2Parts[0]
	if len(module2Parts) == 2 {
		package2, filename2 = module2Parts[0], module2Parts[1]
	}

	// in case both packages are the same, use file names to break ties
	if package1 == package2 {
		return filename1 < filename2
	}

	// in case one of the packages is empty, the empty one goes first
	if len(package1) == 0 || len(package2) == 0 {
		return len(package1) > 0
	}

	// both packages are non-empty and not equal, so compare them
	return package1 < package2
}

func unsortedDictItemsWarning(f *build.File) []*LinterFinding {
	var findings []*LinterFinding

	compareItems := func(item1, item2 *build.KeyValueExpr) bool {
		key1 := item1.Key.(*build.StringExpr).Value
		key2 := item2.Key.(*build.StringExpr).Value
		// regular keys should precede private ones (start with "_")
		if strings.HasPrefix(key1, "_") {
			return strings.HasPrefix(key2, "_") && key1 < key2
		}
		if strings.HasPrefix(key2, "_") {
			return true
		}

		// "//conditions:default" should always be the last
		const conditionsDefault = "//conditions:default"
		if key1 == conditionsDefault {
			return false
		} else if key2 == conditionsDefault {
			return true
		}

		return key1 < key2
	}

	build.WalkPointers(f, func(expr *build.Expr, stack []build.Expr) {
		dict, ok := (*expr).(*build.DictExpr)

		mustSkipCheck := func(expr build.Expr) bool {
			return edit.ContainsComments(expr, "@unsorted-dict-items")
		}

		if !ok || mustSkipCheck(dict) {
			return
		}
		// do not process dictionaries nested within expressions that do not
		// want dict items to be sorted
		for i := len(stack) - 1; i >= 0; i-- {
			if mustSkipCheck(stack[i]) {
				return
			}
		}
		var sortedItems []*build.KeyValueExpr
		for _, item := range dict.List {
			// include only string literal keys into consideration
			if _, ok = item.Key.(*build.StringExpr); !ok {
				continue
			}
			sortedItems = append(sortedItems, item)
		}

		// Fix
		comp := func(i, j int) bool {
			return compareItems(sortedItems[i], sortedItems[j])
		}

		var misplacedItems []*build.KeyValueExpr
		for i := 1; i < len(sortedItems); i++ {
			if comp(i, i-1) {
				misplacedItems = append(misplacedItems, sortedItems[i])
			}
		}

		if len(misplacedItems) == 0 {
			// Already sorted
			return
		}
		newDict := *dict
		newDict.List = append([]*build.KeyValueExpr{}, dict.List...)

		sort.SliceStable(sortedItems, comp)
		sortedItemIndex := 0
		for originalItemIndex := 0; originalItemIndex < len(dict.List); originalItemIndex++ {
			item := dict.List[originalItemIndex]
			if _, ok := item.Key.(*build.StringExpr); !ok {
				continue
			}
			newDict.List[originalItemIndex] = sortedItems[sortedItemIndex]
			sortedItemIndex++
		}

		for _, item := range misplacedItems {
			findings = append(findings, makeLinterFinding(item,
				"Dictionary items are out of their lexicographical order.",
				LinterReplacement{expr, &newDict}))
		}
		return
	})
	return findings
}

// skylarkToStarlark converts a string "skylark" in different cases to "starlark"
// trying to preserve the same case style, e.g. capitalized "Skylark" becomes "Starlark".
func skylarkToStarlark(s string) string {
	switch {
	case s == "SKYLARK":
		return "STARLARK"
	case strings.HasPrefix(s, "S"):
		return "Starlark"
	default:
		return "starlark"
	}
}

// replaceSkylark replaces a substring "skylark" (case-insensitive) with a
// similar cased string "starlark". Doesn't replace it if the previous or the
// next symbol is '/', which may indicate it's a part of a URL.
// Normally that should be done with look-ahead and look-behind assertions in a
// regular expression, but negative look-aheads and look-behinds are not
// supported by Go regexp module.
func replaceSkylark(s string) (newString string, changed bool) {
	skylarkRegex := regexp.MustCompile("(?i)skylark")
	newString = s
	for _, r := range skylarkRegex.FindAllStringIndex(s, -1) {
		if r[0] > 0 && s[r[0]-1] == '/' {
			continue
		}
		if r[1] < len(s)-1 && s[r[1]+1] == '/' {
			continue
		}
		newString = newString[:r[0]] + skylarkToStarlark(newString[r[0]:r[1]]) + newString[r[1]:]
	}
	return newString, newString != s
}

func skylarkCommentWarning(f *build.File) []*LinterFinding {
	var findings []*LinterFinding
	msg := `"Skylark" is an outdated name of the language, please use "starlark" instead.`

	// Check comments
	build.WalkPointers(f, func(expr *build.Expr, stack []build.Expr) {
		comments := (*expr).Comment()
		newComments := build.Comments{
			Before: append([]build.Comment{}, comments.Before...),
			Suffix: append([]build.Comment{}, comments.Suffix...),
			After:  append([]build.Comment{}, comments.After...),
		}
		isModified := false
		var start, end build.Position

		for _, block := range []*[]build.Comment{&newComments.Before, &newComments.Suffix, &newComments.After} {
			for i, comment := range *block {
				// Don't trigger on disabling comments
				if strings.Contains(comment.Token, "disable=skylark-docstring") {
					continue
				}
				newValue, changed := replaceSkylark(comment.Token)
				(*block)[i] = build.Comment{
					Start: comment.Start,
					Token: newValue,
				}
				if changed {
					isModified = true
					start, end = comment.Span()
				}
			}
		}
		if !isModified {
			return
		}
		newExpr := (*expr).Copy()
		newExpr.Comment().Before = newComments.Before
		newExpr.Comment().Suffix = newComments.Suffix
		newExpr.Comment().After = newComments.After
		finding := makeLinterFinding(*expr, msg, LinterReplacement{expr, newExpr})
		finding.Start = start
		finding.End = end
		findings = append(findings, finding)
	})

	return findings
}

func checkSkylarkDocstring(stmts []build.Expr) *LinterFinding {
	msg := `"Skylark" is an outdated name of the language, please use "starlark" instead.`

	doc, ok := getDocstring(stmts)
	if !ok {
		return nil
	}
	docString := (*doc).(*build.StringExpr)
	newValue, updated := replaceSkylark(docString.Value)
	if !updated {
		return nil
	}
	newDocString := *docString
	newDocString.Value = newValue
	return makeLinterFinding(docString, msg, LinterReplacement{doc, &newDocString})
}

func skylarkDocstringWarning(f *build.File) []*LinterFinding {
	var findings []*LinterFinding

	// File docstring
	if finding := checkSkylarkDocstring(f.Stmt); finding != nil {
		findings = append(findings, finding)
	}

	// Function docstrings
	for _, stmt := range f.Stmt {
		def, ok := stmt.(*build.DefStmt)
		if !ok {
			continue
		}
		if finding := checkSkylarkDocstring(def.Body); finding != nil {
			findings = append(findings, finding)
		}
	}

	return findings
}
