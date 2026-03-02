/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/



import cvc5.Basic
import cvc5.TermManager



/-! # Symbol manager -/
namespace cvc5



/-- Opaque symbol manager type. -/
private opaque SymbolManagerImpl : NonemptyType.{0}

/-- Symbol manager.

Internally, this class manages a symbol table and other meta-information pertaining to SMT2 file
inputs (*e.g.* named assertions, declared functions, *etc.*).

A symbol manager can be modified by invoking commands, see `Command.invoke`.

A symbol manager can be provided when constructing an `InputParser`, in which case that
`InputParser` has symbols of this symbol manager preloaded.

The symbol manager's interface is otherwise not publicly available.
-/
def SymbolManager : Type := SymbolManagerImpl.type



namespace SymbolManager

instance : Nonempty SymbolManager := SymbolManagerImpl.property

/-- Constructor.

- `tm` The associated term manager instance.
-/
extern_def new : (tm : TermManager) → Env SymbolManager

end SymbolManager
