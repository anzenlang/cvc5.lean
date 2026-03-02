/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/



import cvc5.Basic




/-! # Solver -/
namespace cvc5



/-- Opaque solver type. -/
private opaque SolverImpl : NonemptyType.{0}

/-- A cvc5 solver. -/
def Solver : Type := SolverImpl.type

namespace Solver

instance : Nonempty Solver := SolverImpl.property

/-- Constructor.

- `tm` The associated term manager instance.
-/
extern_def new : (tm : TermManager) → Env Solver

end Solver
