/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeTensor

/-!
# Exactness of literal tensor extension on finite projectives

Every conflation of finite projective modules splits. Applying the additive
literal tensor functor to that splitting proves exactness for every ring map,
without a flatness assumption and without changing its quotient carrier.

## Implementation provenance

Adapted from the Quillen source
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveTensorBaseChangeExact.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

universe u v

namespace ModuleCat.FiniteProjective

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The literal balanced tensor functor preserves the inherited exact structures. -/
@[colib_tag "COL-1317", colib_ref "quillen"
  "Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveTensorBaseChangeExact.lean:33-38"
  "adaptation"
  "The finite-projective tensor functor preserves conflations without flatness."]
def rightTensorBaseChangeExact (f : R →+* S) :
    ExactFunctor (exactStructure.{u, u} Rᵐᵒᵖ) (exactStructure.{v, max u v} Sᵐᵒᵖ) where
  toFunctor := rightTensorBaseChange f
  map_conflation K hK :=
    (conflation_iff_nonempty_splitting Sᵐᵒᵖ (K.map (rightTensorBaseChange f))).mpr
      ⟨(splittingOfConflation Rᵐᵒᵖ K hK).map (rightTensorBaseChange f)⟩

end ModuleCat.FiniteProjective
