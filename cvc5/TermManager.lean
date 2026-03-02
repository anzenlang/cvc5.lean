/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/



import cvc5.Basic



/-! # Term manager -/
namespace cvc5



/-- Opaque term manager type. -/
private opaque TermManagerImpl : NonemptyType.{0}

/-- Manager for cvc5 terms. -/
def TermManager : Type := TermManagerImpl.type



namespace TermManager

instance : Nonempty TermManager := TermManagerImpl.property

/-- Constructor. -/
extern_def new : Env TermManager

end TermManager
