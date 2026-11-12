/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceBoundary

/-!
# Tests for the same canonical section and its full-boundary coordinate
-/

open CategoryTheory AlgebraicGeometry Stacks.Divisors Opposite

universe u

noncomputable section

variable {X B : Scheme.{u}} (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

local instance differenceInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (differenceSheaf D E) :=
  (isInvertible_differenceSheaf D E).toAlgebraicGeometry

local instance differenceQuasicoherent : (differenceSheaf D E).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_of_isInvertible (differenceSheaf D E)

example : canonicalDifferenceRegularOpen E = E.support.compl :=
  canonicalDifferenceRegularOpen_eq_compl_support E

example : idealSheafSection E (idealOneSection E) =
    (1 : Γ(X, canonicalDifferenceRegularOpen E)) :=
  idealSheafSection_idealOneSection E

example (i : B ⟶ X) (hE : ∀ y : B, i y ∉ E.support) :
    i ⁻¹ᵁ canonicalDifferenceRegularOpen E = ⊤ :=
  preimage_canonicalDifferenceRegularOpen_eq_top i E hE

-- Neither X nor the full boundary B is assumed reduced or integral here.
example (i : B ⟶ X) (hD : ∀ y : B, i y ∉ D.support)
    (hE : ∀ y : B, i y ∉ E.support) :
    (differenceSheafBoundaryIso i D E hD hE).hom.app ⊤
      (canonicalDifferenceBoundaryRegularSection i D E hE) = (1 : Γ(B, ⊤)) :=
  frame_canonicalDifferenceBoundaryRegularSection_eq_one i D E hD hE

-- Only this comparison with the original meromorphic carrier needs integrality.
example [IsIntegral X] : canonicalDifferenceMeromorphicSection D E =
    meromorphicSectionOfConstantGenericStalk X (differenceSheaf D E)
      ((differenceSheaf D E).presheaf.germ (canonicalDifferenceRegularOpen E) (genericPoint X)
        (genericPoint_mem_nonvanishingOpen_canonicalSection E)
        (canonicalDifferenceRegularSection D E)) :=
  canonicalDifferenceMeromorphicSection_eq_regularSection D E

#print axioms Stacks.Divisors.canonicalDifferenceMeromorphicSection_eq_regularSection
#print axioms Stacks.Divisors.regularCanonicalQuotient_eq_tensor
#print axioms Stacks.Divisors.frame_canonicalDifferenceBoundaryRegularSection_eq_one
