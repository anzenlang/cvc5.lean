/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/



import cvc5.Basic



/-! # Terms -/
namespace cvc5



/-- Opaque term type. -/
private opaque TermImpl : NonemptyType.{0}

/-- A cvc5 term. -/
def Term : Type := TermImpl.type



namespace Term

instance : Nonempty Term := TermImpl.property

end Term
