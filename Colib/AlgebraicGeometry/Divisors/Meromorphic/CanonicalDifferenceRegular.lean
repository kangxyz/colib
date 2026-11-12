/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalSectionNonvanishing
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotientGeneric

/-!
# The canonical Cartier-difference section is regular near the full boundary

The ordinary section is constructed on the original canonical denominator's
nonvanishing open. Its generic germ represents the exact canonical meromorphic
section, not just the same divisor class. Every boundary avoiding the negative
divisor lies inside that open, with no reduction of the boundary.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

local instance regularCanonicalPositiveTensorInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (divisorSheaf E) :=
  isTensorInvertible_invertibleSheaf E

local instance regularCanonicalDifferenceInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (differenceSheaf D E) :=
  (isInvertible_differenceSheaf D E).toAlgebraicGeometry

local instance regularCanonicalQuasicoherent (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    L.IsQuasicoherent := isQuasicoherent_of_isInvertible L

/-- The unchanged nonvanishing open of the original positive canonical section of `E`. -/
abbrev canonicalDifferenceRegularOpen : X.Opens :=
  Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
    (divisorSheaf E) (canonicalSection' E)

/-- Ordinary tensor division of the original canonical numerator by the original
canonical denominator, on its actual nonvanishing open. -/
def canonicalDifferenceRegularSection : Γ(differenceSheaf D E, canonicalDifferenceRegularOpen E) :=
  Scheme.Modules.regularTensorQuotientOnNonvanishingOpen X (differenceSheaf D E)
    (divisorSheaf E) (canonicalSection' E) (canonicalDifferenceGlobalNumerator D E)

omit [IsEffectiveCartierDivisor D] in
/-- The ordinary section recovers the original numerator on the whole open. -/
theorem tensorSection_canonicalDifferenceRegularSection :
    Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
      (op (canonicalDifferenceRegularOpen E)) (differenceSheaf D E) (divisorSheaf E)
      (canonicalDifferenceRegularSection D E)
      ((canonicalSection' E).eval (op (canonicalDifferenceRegularOpen E))) =
    (Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E)).presheaf.map
      (homOfLE le_top).op (canonicalDifferenceGlobalNumerator D E) :=
  Scheme.Modules.tensorSection_regularTensorQuotientOnNonvanishingOpen X _ _ _ _

/-- The full source of any morphism avoiding `E` lies inside the regularity neighbourhood. -/
theorem range_subset_canonicalDifferenceRegularOpen {Y : Scheme.{u}} (i : Y ⟶ X)
    (hE : ∀ y : Y, i y ∉ E.support) : Set.range i ⊆ canonicalDifferenceRegularOpen E :=
  range_subset_nonvanishingOpen_canonicalSection E i hE

variable [IsIntegral X]

/-- The ordinary section represents exactly the previously constructed canonical
meromorphic section on the integral total scheme. -/
theorem meromorphicGenericValue_canonicalDifference_eq_germ_regularSection :
    meromorphicGenericValue X (differenceSheaf D E) (canonicalDifferenceMeromorphicSection D E) =
      (differenceSheaf D E).presheaf.germ (canonicalDifferenceRegularOpen E) (genericPoint X)
        (genericPoint_mem_nonvanishingOpen_canonicalSection E)
        (canonicalDifferenceRegularSection D E) := by
  let := Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen X
    (divisorSheaf E) (canonicalSection' E)
  have h := Scheme.Modules.meromorphicGenericValue_quotient_eq_germ_regularTensorQuotient
    X (differenceSheaf D E) (divisorSheaf E) (canonicalSection' E)
    (globalSection_ne_zero_of_isRegularSection _ _ (canonicalSection_isRegular E))
    (canonicalDifferenceRegularOpen E) (genericPoint_mem_nonvanishingOpen_canonicalSection E)
    (canonicalDifferenceGlobalNumerator D E)
  rw [meromorphicSectionOfGlobalSection_canonicalDifferenceGlobalNumerator] at h
  exact h

/-- Equality in the native meromorphic-section carrier follows from the original generic
germ. No Weil-divisor or Picard-class identification is used here. -/
theorem canonicalDifferenceMeromorphicSection_eq_regularSection :
    canonicalDifferenceMeromorphicSection D E =
      meromorphicSectionOfConstantGenericStalk X (differenceSheaf D E)
        ((differenceSheaf D E).presheaf.germ (canonicalDifferenceRegularOpen E) (genericPoint X)
          (genericPoint_mem_nonvanishingOpen_canonicalSection E)
          (canonicalDifferenceRegularSection D E)) := by
  apply meromorphicGenericValue_injective X (differenceSheaf D E)
  rw [meromorphicGenericValue_meromorphicSectionOfConstantGenericStalk]
  exact meromorphicGenericValue_canonicalDifference_eq_germ_regularSection D E

end Stacks.Divisors
