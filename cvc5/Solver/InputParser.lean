/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/



import cvc5.Basic
import cvc5.Solver.Defs
import cvc5.Solver.SymbolManager



/-! # Operators -/
namespace cvc5



/-- Opaque operator type. -/
private opaque InputParserImpl : NonemptyType.{0}

/-- This type is the main interface for retrieving commands and expressions from an input using a
  parser.

After construction, it is expected that an input is first configured via, e.g.,
`InputParser.setFileInput`, `InputParser.setStreamInput`, `InputParser.setStringInput` or
`InputParser.setIncrementalStringInput` and `InputParser.appendIncrementalStringInput`. Then,
functions `InputParser.nextCommand` and `InputParser.nextExpression` can be invoked to parse the
input.

The input parser interacts with a symbol manager, which determines which symbols are defined in the
current context, based on the background logic and user-defined symbols. If no symbol manager is
provided, then the input parser will construct (an initially empty) one.

If provided, the symbol manager must have a logic that is compatible with the provided solver. That
is, if both the solver and symbol manager have their logics set (`SymbolManager.isLogicSet` and
`Solver.isLogicSet`), then their logics must be the same.

Upon setting an input source, if either the solver (resp. symbol manager) has its logic set, then
the symbol manager (resp. solver) is set to use that logic, if its logic is not already set.
-/
def InputParser : Type := InputParserImpl.type



namespace InputParser

instance : Nonempty InputParser := InputParserImpl.property

/-- Construct an input parser with an initially empty symbol manager.

- `solver`: The solver (e.g. for constructing terms and sorts).
-/
private extern_def ofSolver : (solver : Solver) → Env InputParser

/-- Construct an input parser.

- `solver` The solver (e.g. for constructing terms and sorts).
- `sm` The symbol manager, which contains a symbol table that maps symbols to terms and sorts. Must
  have a logic that is compatible with the solver.
-/
private extern_def ofSolverAndSM : (solver : Solver) → (sm : SymbolManager) → Env InputParser

@[inherit_doc ofSolverAndSM]
def new (solver : Solver) : (sm : Option SymbolManager := none) → Env InputParser
  | none => ofSolver solver
  | some sm => ofSolverAndSM solver sm

end InputParser
