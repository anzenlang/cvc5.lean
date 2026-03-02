/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/



import cvc5.Basic



/-! # Proofs -/
namespace cvc5



/-- Opaque proof type. -/
private opaque ProofImpl : NonemptyType.{0}

/-- A cvc5 proof.

Proofs are trees and every proof object corresponds to the root step of a proof. The branches of the
root step are the premises of the step.
-/
def Proof : Type := ProofImpl.type


namespace Proof

instance : Nonempty Proof := ProofImpl.property

end Proof
