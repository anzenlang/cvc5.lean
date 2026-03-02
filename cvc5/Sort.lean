/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/



import cvc5.Basic



/-! # Sorts -/
namespace cvc5



/-- Opaque sort type. -/
private opaque SortImpl : NonemptyType.{0}

/-- The sort of a cvc5 term. -/
def «Sort» : Type := cvc5.SortImpl.type



namespace «Sort»

instance : Nonempty cvc5.Sort := SortImpl.property

end «Sort»
