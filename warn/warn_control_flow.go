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

// Warnings related to the control flow

package warn

import (
	"fmt"
	"strings"

	"github.com/please-build/buildtools/build"
	"github.com/please-build/buildtools/bzlenv"
	"github.com/please-build/buildtools/edit"
)

// findReturnsWithoutValue searches for return statements without a value, calls `callback` on
// them and returns whether the current list of statements terminates (either by a return or fail()
// statements on the current level in all subbranches.
func findReturnsWithoutValue(stmts []build.Expr, callback func(*build.ReturnStmt)) bool {
	if len(stmts) == 0 {
		// May occur in empty else-clauses
		return false
	}
	terminated := false
	for _, stmt := range stmts {
		switch stmt := stmt.(type) {
		case *build.ReturnStmt:
			if stmt.Result == nil {
				callback(stmt)
			}
			terminated = true
		case *build.CallExpr:
			ident, ok := stmt.X.(*build.Ident)
			if ok && ident.Name == "fail" {
				terminated = true
			}
		case *build.ForStmt:
			// Call recursively to find all return statements without a value there.
			// Even if a for-loop is guaranteed to terminate in each iteration, buildifier still can't
			// check whether the loop is not empty, so we can't say that the statement after the ForStmt
			// is unreachable.
			findReturnsWithoutValue(stmt.Body, callback)
		case *build.IfStmt:
			// Save to separate values to avoid short circuit evaluation
			term1 := findReturnsWithoutValue(stmt.True, callback)
			term2 := findReturnsWithoutValue(stmt.False, callback)
			if term1 && term2 {
				terminated = true
			}
		}
	}
	return terminated
}

// missingReturnValueWarning warns if a function returns both explicit and implicit values.
func missingReturnValueWarning(f *build.File) []*LinterFinding {
	findings := []*LinterFinding{}

	// Collect all def statements in the file
	defStmts := []*build.DefStmt{}
	build.WalkStatements(f, func(expr build.Expr, stack []build.Expr) (err error) {
		if def, ok := expr.(*build.DefStmt); ok {
			defStmts = append(defStmts, def)
		}
		return
	})

	for _, function := range defStmts {
		var hasNonEmptyReturns bool
		build.WalkStatements(function, func(expr build.Expr, stack []build.Expr) (err error) {
			if _, ok := expr.(*build.DefStmt); ok {
				if len(stack) > 0 {
					return &build.StopTraversalError{}
				}
			}

			if ret, ok := expr.(*build.ReturnStmt); ok && ret.Result != nil {
				hasNonEmptyReturns = true
			}
			return err
		})

		if !hasNonEmptyReturns {
			continue
		}
		explicitReturn := findReturnsWithoutValue(function.Body, func(ret *build.ReturnStmt) {
			findings = append(findings,
				makeLinterFinding(ret, fmt.Sprintf("Some but not all execution paths of %q return a value.", function.Name)))
		})
		if !explicitReturn {
			findings = append(findings,
				makeLinterFinding(function, fmt.Sprintf(`Some but not all execution paths of %q return a value.
The function may terminate by an implicit return in the end.`, function.Name)))
		}
	}
	return findings
}

// findUnreachableStatements searches for unreachable statements (i.e. statements that immediately
// follow `return`, `break`, `continue`, and `fail()` statements and calls `callback` on them.
// If there are several consequent unreachable statements, it only reports the first of them.
// Returns whether the execution is terminated explicitly.
func findUnreachableStatements(stmts []build.Expr, callback func(build.Expr)) bool {
	unreachable := false
	for _, stmt := range stmts {
		if unreachable {
			callback(stmt)
			return true
		}
		switch stmt := stmt.(type) {
		case *build.ReturnStmt:
			unreachable = true
		case *build.CallExpr:
			ident, ok := stmt.X.(*build.Ident)
			if ok && ident.Name == "fail" {
				unreachable = true
			}
		case *build.BranchStmt:
			if stmt.Token != "pass" {
				// either break or continue
				unreachable = true
			}
		case *build.ForStmt:
			findUnreachableStatements(stmt.Body, callback)
		case *build.IfStmt:
			// Save to separate values to avoid short circuit evaluation
			term1 := findUnreachableStatements(stmt.True, callback)
			term2 := findUnreachableStatements(stmt.False, callback)
			if term1 && term2 {
				unreachable = true
			}
		}
	}
	return unreachable
}

func unreachableStatementWarning(f *build.File) []*LinterFinding {
	findings := []*LinterFinding{}

	build.WalkStatements(f, func(expr build.Expr, stack []build.Expr) (err error) {
		def, ok := expr.(*build.DefStmt)
		if !ok {
			return
		}
		findUnreachableStatements(def.Body, func(expr build.Expr) {
			findings = append(findings,
				makeLinterFinding(expr, `The statement is unreachable.`))
		})
		return
	})
	return findings
}

func noEffectStatementsCheck(body []build.Expr, isTopLevel, isFunc bool, findings []*LinterFinding) []*LinterFinding {
	seenNonComment := false
	for _, stmt := range body {
		if stmt == nil {
			continue
		}

		_, isString := stmt.(*build.StringExpr)
		if isString {
			if !seenNonComment && (isTopLevel || isFunc) {
				// It's a docstring.
				seenNonComment = true
				continue
			}
		}
		if _, ok := stmt.(*build.CommentBlock); !ok {
			seenNonComment = true
		}
		switch s := (stmt).(type) {
		case *build.DefStmt, *build.ForStmt, *build.IfStmt, *build.ReturnStmt,
			*build.CallExpr, *build.CommentBlock, *build.BranchStmt, *build.AssignExpr:
			continue
		case *build.Comprehension:
			if !isTopLevel || s.Curly {
				// List comprehensions are allowed on top-level.
				findings = append(findings,
					makeLinterFinding(stmt, "Expression result is not used. Use a for-loop instead of a list comprehension."))
			}
			continue
		}

		msg := "Expression result is not used."
		if isString {
			msg += " Docstrings should be the first statements of a file or a function (they may follow comment lines)."
		}
		findings = append(findings, makeLinterFinding(stmt, msg))
	}
	return findings
}

func noEffectWarning(f *build.File) []*LinterFinding {
	findings := []*LinterFinding{}
	findings = noEffectStatementsCheck(f.Stmt, true, false, findings)
	build.WalkStatements(f, func(expr build.Expr, stack []build.Expr) (err error) {
		// Docstrings are valid statements without effects. To detect them we need to
		// analyze blocks of statements rather than single statements.
		switch expr := expr.(type) {
		case *build.ForStmt:
			findings = noEffectStatementsCheck(expr.Body, false, false, findings)
		case *build.DefStmt:
			findings = noEffectStatementsCheck(expr.Function.Body, false, true, findings)
		case *build.IfStmt:
			findings = noEffectStatementsCheck(expr.True, false, false, findings)
			findings = noEffectStatementsCheck(expr.False, false, false, findings)
		}
		return
	})
	return findings
}

// extractIdentsFromStmt returns all idents from the an AST node representing a
// single statement that are either defined outside the node and used inside,
// or defined inside the node and can be used outside.
// Examples of idents that don't fall into either of the categories:
//   * Named arguments of function calls: `foo` in `f(foo = "bar")`
//   * Iterators of comprehension nodes and its usages: `x` in `[f(x) for x in y]`
// Statements that contain other statements (for-loops, if-else blocks) are not
// traversed inside.
func extractIdentsFromStmt(stmt build.Expr) (assigned, used map[*build.Ident]bool) {
	// The values for `assigned` are `true` if the warning for the variable should
	// be suppressed, and `false` otherwise.
	// It's still important to know that the variable has been assigned in the
	// current scope because it could shadow a variable with the same name from an
	// outer scope.
	assigned = make(map[*build.Ident]bool)
	used = make(map[*build.Ident]bool)

	// Local scopes for comprehensions
	scopes := make(map[build.Expr]map[string]bool)

	// Nodes that are excluded from traversal
	blockedNodes := make(map[build.Expr]bool)

	build.WalkInterruptable(stmt, func(node build.Expr, stack []build.Expr) (err error) {
		// Check if the current node has been blocked
		if _, ok := blockedNodes[node]; ok {
			return &build.StopTraversalError{}
		}

		switch expr := node.(type) {
		case *build.AssignExpr:
			// If it's a top-level assign expression, extract LValues from LHS
			// Otherwise just ignore the LHS, it must be a keyword argument of a
			// function call.
			if node != stmt {
				// The assignment expression is not the statement itself but its child,
				// that means it's a keyword argument for a function call. Its LHS
				// should be ignored.
				blockedNodes[expr.LHS] = true
				return
			}

			hasUnusedComment := edit.ContainsComments(expr, "@unused")

			// LHS may contain both variables that are being used and variables that
			// are being assigned to, e.g. in the following example:
			//     x[i][f(name='foo')], y = 1, 2
			// `x`, `i`, `f` are used, `y` is assigned, `name` should be ignored.
			// Further traversal will ignore `name` but won't know that it's in an LHS
			// of an assign expression, so it'll erroneously collect `y` as used.
			// After the traversal it'll need to be removed from `used`.

			// If some (but not all) variables assigned to by the statements are
			// prefixed with an underscore, suppress the warning on them (i.e. allow
			// them to be unused). That's a common use case for partial unpacking of
			// tuples:
			//
			//     foo, _bar = my_function()  # only `foo` is needed
			//
			// However if all variables are underscored and unused, they should still
			// be reported:
			//
			//     _foo, _bar = my_function()  # LHS can just be removed

			lValues := bzlenv.CollectLValues(expr.LHS)
			allLValuesUnderscored := true
			for _, lValue := range lValues {
				if !strings.HasPrefix(lValue.Name, "_") {
					allLValuesUnderscored = false
					break
				}
			}

			for _, lValue := range bzlenv.CollectLValues(expr.LHS) {
				assigned[lValue] = hasUnusedComment ||
					(!allLValuesUnderscored && strings.HasPrefix(lValue.Name, "_"))
			}

		case *build.ForStmt:
			// Like AssignExpr, ForStmt too have an analogue of LHS and RHS.
			// Unlike AssignExpr, in this function they may appear only in the root of
			// traversal and shouldn't be traversed inside (the caller of
			// `extractIdentsFromStmt` should be responsible for checking all
			// statements including those that are inside for-loops.

			// It's common to not use all variables (or even not use any of them)
			// after unpacking tuples, suppress the warning an all of them that are
			// prefixed with an underscore:
			//
			//     for _, (_b, c) in iterable:
			//         print(c)
			for _, lValue := range bzlenv.CollectLValues(expr.Vars) {
				assigned[lValue] = strings.HasPrefix(lValue.Name, "_")
			}

			// Don't traverse inside the inner statements (but still traverse into
			// the expressions in `Vars` an `X`).
			for _, substmt := range expr.Body {
				blockedNodes[substmt] = true
			}

		case *build.IfStmt:
			// Nothing special, just don't traverse the inner statements (like with
			// ForStmt nodes).
			for _, substmt := range expr.True {
				blockedNodes[substmt] = true
			}
			for _, substmt := range expr.False {
				blockedNodes[substmt] = true
			}

		case *build.Comprehension:
			// Comprehensions introduce their own visibility scope that shadows the
			// outer scope. Iterators that are defined and used there don't affect
			// the usage of variables with the same name outside the comprehension
			// scope.
			scope := make(map[string]bool)
			for _, clause := range expr.Clauses {
				forClause, ok := clause.(*build.ForClause)
				if !ok {
					// if-clause
					continue
				}
				for _, lValue := range bzlenv.CollectLValues(forClause.Vars) {
					scope[lValue.Name] = true
				}
			}
			scopes[expr] = scope
		case *build.Ident:
			// If the identifier is defined in an intermediate scope, ignore it.
			for _, node := range stack {
				if scope, ok := scopes[node]; ok {
					if _, ok := scope[expr.Name]; ok {
						return
					}
				}
			}
			used[expr] = true

		default:
			// Do nothing, just traverse further
		}
		return
	})

	for ident := range assigned {
		// If the same ident (not the same variable but the same AST node) is
		// registered as both "assigned" and "used", it means it was in fact just
		// assigned, remove it from "used".
		delete(used, ident)
	}
	return assigned, used
}

// unusedVariableCheck checks for unused variables inside a given node `stmt` (either *build.File or
// *build.DefStmt) and variables that are used in the current scope or subscopes,
// but not defined here.
func unusedVariableCheck(f *build.File, root build.Expr) (map[string]bool, []*LinterFinding) {
	findings := []*LinterFinding{}

	// Symbols that are defined in the current scope
	definedSymbols := make(map[string]*build.Ident)

	// Functions that are defined in the current scope
	definedFunctions := make(map[string]*build.DefStmt)

	// Symbols that are used in the current and inner scopes
	usedSymbols := make(map[string]bool)

	// Symbols for which the warning should be suppressed
	suppressedWarnings := make(map[string]bool)

	build.WalkStatements(root, func(expr build.Expr, stack []build.Expr) (err error) {
		switch expr := expr.(type) {
		case *build.File:
			// File nodes don't have anything meaningful, just traverse its subnodes.

		case *build.DefStmt:
			if len(stack) > 0 {
				// Nested def statement. Don't traverse inside, instead call
				// unusedVariableCheck recursively to handle nested scopes properly.

				// The function name is defined in the current scope
				if _, ok := definedFunctions[expr.Name]; !ok {
					definedFunctions[expr.Name] = expr
				}
				if edit.ContainsComments(expr, "@unused") {
					suppressedWarnings[expr.Name] = true
				}

				usedSymbolsInFunction, findingsInFunction := unusedVariableCheck(f, expr)
				findings = append(findings, findingsInFunction...)
				for symbol := range usedSymbolsInFunction {
					usedSymbols[symbol] = true
				}
				return &build.StopTraversalError{}
			}

			// The function is a root for the current scope.
			// Collect its parameters as defined in the current scope.
			for _, param := range expr.Params {
				// Function parameters are defined in the current scope.
				if ident, _ := build.GetParamIdent(param); ident != nil {
					definedSymbols[ident.Name] = ident
					if strings.HasPrefix(ident.Name, "_") || edit.ContainsComments(param, "@unused") {
						// Don't warn about function arguments if they start with "_"
						// or explicitly marked with @unused
						suppressedWarnings[ident.Name] = true
					}
				}
				// The default variables for the parameters are defined in the outer
				// scope but used here.
				assign, ok := param.(*build.AssignExpr)
				if !ok {
					continue
				}

				// RHS is not a statement, but similar traversal rules should be applied
				// to it. E.g. it may have a comprehension node with its inner scope or
				// a function call with a keyword parameter.
				_, used := extractIdentsFromStmt(assign.RHS)
				for ident := range used {
					usedSymbols[ident.Name] = true
				}
			}

		default:
			assigned, used := extractIdentsFromStmt(expr)

			for symbol := range used {
				usedSymbols[symbol.Name] = true
			}
			for symbol, isSuppressed := range assigned {
				if _, ok := definedSymbols[symbol.Name]; !ok {
					definedSymbols[symbol.Name] = symbol
					if isSuppressed {
						suppressedWarnings[symbol.Name] = true
					}
				}
			}
		}
		return
	})

	// If a variable is defined in an outer scope but also in this scope, it
	// shadows the outer variable. If it's used in the current scope, it doesn't
	// make the variable with the same name from an outer scope also used.
	// Collect variables that are used in the current or inner scopes but are not
	// defined in the current scope.
	usedSymbolsFromOuterScope := make(map[string]bool)
	for symbol := range usedSymbols {
		if _, ok := definedSymbols[symbol]; ok {
			continue
		}
		if _, ok := definedFunctions[symbol]; ok {
			continue
		}
		usedSymbolsFromOuterScope[symbol] = true
	}

	// Top-level variables defined in .bzl or generic Starlark files
	// can be imported from elsewhere, even if not used in the current file.
	// Do not warn on exportable variables.
	ignoreTopLevel := (f.Type == build.TypeBzl || f.Type == build.TypeDefault) && root == f

	for name, ident := range definedSymbols {
		if _, ok := usedSymbols[name]; ok {
			// The variable is used either in this scope or in a nested scope
			continue
		}
		if _, ok := suppressedWarnings[name]; ok {
			// The variable is explicitly marked with @unused, ignore
			continue
		}
		if ignoreTopLevel && !strings.HasPrefix(name, "_") {
			continue
		}
		findings = append(findings,
			makeLinterFinding(ident, fmt.Sprintf(`Variable %q is unused. Please remove it.`, ident.Name)))
	}

	for name, def := range definedFunctions {
		if _, ok := usedSymbols[name]; ok {
			// The function is used either in this scope or in a nested scope
			continue
		}
		if ignoreTopLevel && !strings.HasPrefix(name, "_") {
			continue
		}
		if _, ok := suppressedWarnings[name]; ok {
			// The function is explicitly marked with @unused, ignore
			continue
		}
		findings = append(findings,
			makeLinterFinding(def, fmt.Sprintf(`Function %q is unused. Please remove it.`, def.Name)))
	}

	return usedSymbolsFromOuterScope, findings
}

func unusedVariableWarning(f *build.File) []*LinterFinding {
	_, findings := unusedVariableCheck(f, f)
	return findings
}

func redefinedVariableWarning(f *build.File) []*LinterFinding {
	findings := []*LinterFinding{}
	definedSymbols := make(map[string]bool)

	types := detectTypes(f)
	for _, s := range f.Stmt {
		// look for all assignments in the scope
		as, ok := s.(*build.AssignExpr)
		if !ok {
			continue
		}
		left, ok := as.LHS.(*build.Ident)
		if !ok {
			continue
		}
		if !definedSymbols[left.Name] {
			definedSymbols[left.Name] = true
			continue
		}

		if as.Op == "+=" && (types[as.LHS] == List || types[as.RHS] == List) {
			// Not a reassignment, just appending to a list
			continue
		}

		findings = append(findings,
			makeLinterFinding(as.LHS, fmt.Sprintf(`Variable %q has already been defined. 
Redefining a global value is discouraged and will be forbidden in the future.
Consider using a new variable instead.`, left.Name)))
	}
	return findings
}

// collectLocalVariables traverses statements (e.g. of a function definition) and returns a list
// of idents for variables defined anywhere inside the function.
func collectLocalVariables(stmts []build.Expr) []*build.Ident {
	variables := []*build.Ident{}

	for _, stmt := range stmts {
		switch stmt := stmt.(type) {
		case *build.DefStmt:
			// Don't traverse nested functions
		case *build.ForStmt:
			variables = append(variables, bzlenv.CollectLValues(stmt.Vars)...)
			variables = append(variables, collectLocalVariables(stmt.Body)...)
		case *build.IfStmt:
			variables = append(variables, collectLocalVariables(stmt.True)...)
			variables = append(variables, collectLocalVariables(stmt.False)...)
		case *build.AssignExpr:
			variables = append(variables, bzlenv.CollectLValues(stmt.LHS)...)
		}
	}
	return variables
}

// searchUninitializedVariables takes a list of statements (e.g. body of a block statement)
// and a map of previously initialized statements, and calls `callback` on all idents that are not
// initialized. An ident is considered initialized if it's initialized by every possible execution
// path (before or by `stmts`).
// Returns a boolean indicating whether the current list of statements is guaranteed to be
// terminated explicitly (by return or fail() statements) and a map of variables that are guaranteed
// to be defined by `stmts`.
func findUninitializedVariables(stmts []build.Expr, previouslyInitialized map[string]bool, callback func(*build.Ident)) (bool, map[string]bool) {
	// Variables that are guaranteed to be initialized
	locallyInitialized := make(map[string]bool) // in the local block of `stmts`
	initialized := make(map[string]bool)        // anywhere before the current line
	for key := range previouslyInitialized {
		initialized[key] = true
	}

	// findUninitializedIdents traverses an expression (simple statement or a part of it), and calls
	// `callback` on every *build.Ident that's not mentioned in the map of initialized variables
	findUninitializedIdents := func(expr build.Expr, callback func(ident *build.Ident)) {
		// Collect lValues, they shouldn't be taken into account
		// For example, if the expression is `a = foo(b = c)`, only `c` can be an uninitialized variable here.
		lValues := make(map[*build.Ident]bool)
		build.WalkInterruptable(expr, func(expr build.Expr, stack []build.Expr) (err error) {
			switch expr := expr.(type) {
			case *build.DefStmt:
				// Function arguments can't be uninitialized, even if they share the same
				// name with a variable that's not initialized for some execution path
				// in an outer scope.
				for _, param := range expr.Params {
					if ident, _ := build.GetParamIdent(param); ident != nil {
						lValues[ident] = true
					}
				}
				// Don't traverse into nested def statements
				return &build.StopTraversalError{}
			case *build.AssignExpr:
				for _, ident := range bzlenv.CollectLValues(expr.LHS) {
					lValues[ident] = true
				}
			}
			return
		})

		// Check if the ident is really not initialized and call the callback on it.
		callbackIfNeeded := func(ident *build.Ident) {
			if !initialized[ident.Name] && !lValues[ident] {
				callback(ident)
			}
		}

		build.WalkInterruptable(expr, func(expr build.Expr, stack []build.Expr) (err error) {
			switch expr := expr.(type) {
			case *build.Comprehension:
				// Comprehension nodes are special, they have their own scope with variables
				// that are only defined inside. Instead of traversing inside stop the
				// traversal and call a special function to retrieve idents from the outer
				// scope that are used inside the comprehension.

				_, used := extractIdentsFromStmt(expr)
				for ident := range used {
					callbackIfNeeded(ident)
				}

				return &build.StopTraversalError{}
			case *build.Ident:
				callbackIfNeeded(expr)
			default:
				// Just traverse further
			}
			return
		})
	}

	for _, stmt := range stmts {
		newlyDefinedVariables := make(map[string]bool)
		switch stmt := stmt.(type) {
		case *build.DefStmt:
			// Don't traverse nested functions
		case *build.CallExpr:
			if _, ok := isFunctionCall(stmt, "fail"); ok {
				return true, locallyInitialized
			}
		case *build.ReturnStmt:
			findUninitializedIdents(stmt, callback)
			return true, locallyInitialized
		case *build.BranchStmt:
			if stmt.Token == "break" || stmt.Token == "continue" {
				return true, locallyInitialized
			}
		case *build.ForStmt:
			// Although loop variables are defined as local variables, buildifier doesn't know whether
			// the collection will be empty or not.

			// Traverse but ignore the result. Even if something is defined inside a for-loop, the loop
			// may be empty and the variable initialization may not happen.
			findUninitializedIdents(stmt.X, callback)

			// The loop can access the variables defined above, and also the for-loop variables.
			initializedInLoop := make(map[string]bool)
			for name := range initialized {
				initializedInLoop[name] = true
			}
			for _, ident := range bzlenv.CollectLValues(stmt.Vars) {
				initializedInLoop[ident.Name] = true
			}
			findUninitializedVariables(stmt.Body, initializedInLoop, callback)
			continue
		case *build.IfStmt:
			findUninitializedIdents(stmt.Cond, callback)
			// Check the variables defined in the if- and else-clauses.
			terminatedTrue, definedInTrue := findUninitializedVariables(stmt.True, initialized, callback)
			terminatedFalse, definedInFalse := findUninitializedVariables(stmt.False, initialized, callback)
			if terminatedTrue && terminatedFalse {
				return true, locallyInitialized
			} else if terminatedTrue {
				// Only take definedInFalse into account
				for key := range definedInFalse {
					locallyInitialized[key] = true
					initialized[key] = true
				}
			} else if terminatedFalse {
				// Only take definedInTrue into account
				for key := range definedInTrue {
					locallyInitialized[key] = true
					initialized[key] = true
				}
			} else {
				// If a variable is defined in both if- and else-clauses, it's considered as defined
				for key := range definedInTrue {
					if definedInFalse[key] {
						locallyInitialized[key] = true
						initialized[key] = true
					}
				}
			}
			continue
		case *build.AssignExpr:
			// Assignment expression. Collect all definitions from the lhs
			for _, ident := range bzlenv.CollectLValues(stmt.LHS) {
				newlyDefinedVariables[ident.Name] = true
			}
		}
		findUninitializedIdents(stmt, callback)
		for name := range newlyDefinedVariables {
			locallyInitialized[name] = true
			initialized[name] = true
		}
	}
	return false, locallyInitialized
}

// uninitializedVariableWarning warns about usages of values that may not have been initialized.
func uninitializedVariableWarning(f *build.File) []*LinterFinding {
	findings := []*LinterFinding{}
	build.WalkStatements(f, func(expr build.Expr, stack []build.Expr) (err error) {
		def, ok := expr.(*build.DefStmt)
		if !ok {
			return
		}

		// Get all variables defined in the function body.
		// If a variable is not defined there, it can be builtin, global, or loaded.
		localVars := make(map[string]bool)
		for _, ident := range collectLocalVariables(def.Body) {
			localVars[ident.Name] = true
		}

		// Function parameters are guaranteed to be defined everywhere in the function, even if they
		// are redefined inside the function body. They shouldn't be taken into consideration.
		for _, param := range def.Params {
			if name, _ := build.GetParamName(param); name != "" {
				delete(localVars, name)
			}
		}

		// Search for all potentially initialized variables in the function body
		findUninitializedVariables(def.Body, make(map[string]bool), func(ident *build.Ident) {
			// Check that the found ident represents a local variable
			if localVars[ident.Name] {
				findings = append(findings,
					makeLinterFinding(ident, fmt.Sprintf(`Variable "%s" may not have been initialized.`, ident.Name)))
			}
		})
		return
	})
	return findings
}
