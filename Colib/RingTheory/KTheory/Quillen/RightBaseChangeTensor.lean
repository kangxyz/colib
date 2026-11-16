/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveTensorBaseChangeExact
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
public import Colib.KTheory.Quillen.Map.NaturalIso

/-!
# Literal tensor extension gives the original K-map

The canonical natural isomorphism identifies tensor extension with the unchanged
matrix-image exact functor. Natural-isomorphism invariance compares the original
zero-normalized K-maps in every degree. Both rings have a common universe, as
required by the existing K-map interface; no mixed-universe identification of
finite-projective categories is asserted.

## Implementation provenance

Adapted from the Quillen source
`Quillen/KTheory/Map/RightBaseChangeTensor.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

universe u

namespace ModuleCat.FiniteProjective

variable {R S : Type u} [Ring R] [Ring S]

/-- Literal tensor scalar extension induces the original K-map in every degree. -/
@[colib_tag "COL-1294",
  colib_ref "quillen" "Quillen/KTheory/Map/RightBaseChangeTensor.lean:33-36" "adaptation"
    "Equality of the two indicated zero-normalized K-maps in every natural degree.",
  colib_ref "WeibelKBook" "II, Additive Functors 2.8 and Example 2.8.1" "background"
  "Tensor base change on finite projective right modules and its degree-zero K-map"]
theorem rightTensorBaseChangeExact_KMap (f : R →+* S) (n : ℕ) :
    (rightTensorBaseChangeExact f).KMap n = (rightBaseChangeExact f).KMap n :=
  CategoryTheory.ExactCategory.ExactFunctor.KMap_eq_of_natIso (F := rightTensorBaseChangeExact f)
    (G := rightBaseChangeExact f) (rightTensorBaseChangeIso f) n

end ModuleCat.FiniteProjective
