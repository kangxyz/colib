/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafPicard
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalSection
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport

/-!
# The canonical meromorphic section of a Cartier difference

The module is the literal `differenceSheaf D E = 𝒪(D) ⊗ ℐ_E`. Native evaluation
identifies its tensor product with `𝒪(E)` with `𝒪(D)`. Dividing the transported
canonical section of `𝒪(D)` by the canonical section of `𝒪(E)` constructs a regular
meromorphic section. Its divisor is the original Cartier difference, with full
local quotient lengths and the positive-minus-negative convention.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

local instance canonicalDifferenceInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (differenceSheaf D E) :=
  (isInvertible_differenceSheaf D E).toAlgebraicGeometry

local instance canonicalDifferenceTensorInvertible (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L N) := by
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : AlgebraicGeometry.SheafOfModules.IsInvertible
      X.sheaf.obj X.ringCatSheaf.property L)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : AlgebraicGeometry.SheafOfModules.IsInvertible
      X.sheaf.obj X.ringCatSheaf.property N)
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj
    X.ringCatSheaf.property L N).toAlgebraicGeometry

local instance canonicalDifferenceQuasicoherent (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    L.IsQuasicoherent := isQuasicoherent_of_isInvertible L

/-- Native associativity, symmetry and evaluation cancel the actual Cartier ideal
against its dual. The first factor remains the original positive divisor sheaf. -/
def differenceSheafTensorPositiveIso :
    Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E) ≅ divisorSheaf D := by
  have := isTensorInvertible_negativeTwist E
  exact Stacks.SheafOfModules.Invertible.tensorProductAssociator X.sheaf.obj
      X.ringCatSheaf.property (divisorSheaf D) (negativeTwist' E) (divisorSheaf E) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property
      (Iso.refl _) (Stacks.SheafOfModules.tensorSheafBraiding X.sheaf.obj
        X.ringCatSheaf.property (negativeTwist' E) (divisorSheaf E) ≪≫
          Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' E)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.sheaf.obj
      X.ringCatSheaf.property (divisorSheaf D)

variable [IsIntegral X]

/-- The canonical numerator, transported through the native Cartier evaluation isomorphism. -/
def canonicalDifferenceNumerator : MeromorphicSection X.sheaf
    (Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E)) :=
  mapMeromorphicSection _ _ (differenceSheafTensorPositiveIso D E).inv
    (canonicalMeromorphicSection D)

/-- Transport through the specified isomorphism preserves regularity. -/
theorem isRegularMeromorphicSection_canonicalDifferenceNumerator :
    IsRegularMeromorphicSection X.sheaf
      (Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E))
      (canonicalDifferenceNumerator D E) :=
  isRegularMeromorphicSection_mapMeromorphicSection _ _
    (differenceSheafTensorPositiveIso D E).symm _
      (isRegularMeromorphicSection_canonicalMeromorphicSection D)

/-- The canonical regular meromorphic section of the actual Cartier difference module. -/
@[colib_tag "COL-1050", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/SectionTransport.lean:89-110"
  "ingredient" "Transport and regularity of the canonical numerator; the Cartier-difference \
    quotient is constructed here."]
def canonicalDifferenceMeromorphicSection : MeromorphicSection X.sheaf (differenceSheaf D E) :=
  quotientTensorMeromorphicSection X (differenceSheaf D E) (divisorSheaf E)
    (canonicalDifferenceNumerator D E) (canonicalMeromorphicSection E)
    (isRegularMeromorphicSection_canonicalMeromorphicSection E)

/-- The canonical Cartier-difference section is regular. -/
theorem isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection :
    IsRegularMeromorphicSection X.sheaf (differenceSheaf D E)
      (canonicalDifferenceMeromorphicSection D E) :=
  isRegularMeromorphicSection_quotientTensorMeromorphicSection X _ _ _ _
    (isRegularMeromorphicSection_canonicalDifferenceNumerator D E)
    (isRegularMeromorphicSection_canonicalMeromorphicSection E)

/-- The defining equation uses the two original canonical sections and the native
Cartier pairing, not an equation of divisor classes. -/
theorem tensorMeromorphicSection_canonicalDifferenceMeromorphicSection :
    tensorMeromorphicSection X (differenceSheaf D E) (divisorSheaf E)
        (canonicalDifferenceMeromorphicSection D E) (canonicalMeromorphicSection E) =
      canonicalDifferenceNumerator D E :=
  tensorMeromorphicSection_quotientTensorMeromorphicSection X _ _ _ _ _


/-- The literal Weil divisor of the canonical difference section is the difference
of the two original canonical Cartier-section divisors. -/
theorem weilDivisorOfMeromorphicSection_canonicalDifference_eq_sub
    [IsLocallyNoetherian X] :
    AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf D E)
        (canonicalDifferenceMeromorphicSection D E)
        (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E) =
      AlgebraicGeometry.weilDivisorOfMeromorphicSection X (divisorSheaf D)
        (canonicalMeromorphicSection D)
        (isRegularMeromorphicSection_canonicalMeromorphicSection D) -
      AlgebraicGeometry.weilDivisorOfMeromorphicSection X (divisorSheaf E)
        (canonicalMeromorphicSection E)
        (isRegularMeromorphicSection_canonicalMeromorphicSection E) := by
  exact (weilDivisorOfMeromorphicSection_quotientTensorMeromorphicSection X
    (differenceSheaf D E) (divisorSheaf E) (canonicalDifferenceNumerator D E)
    (canonicalMeromorphicSection E) (isRegularMeromorphicSection_canonicalDifferenceNumerator D E)
    (isRegularMeromorphicSection_canonicalMeromorphicSection E)).trans
      (congrArg (fun A => A - AlgebraicGeometry.weilDivisorOfMeromorphicSection X
        (divisorSheaf E) (canonicalMeromorphicSection E)
        (isRegularMeromorphicSection_canonicalMeromorphicSection E))
        (weilDivisorOfMeromorphicSection_mapMeromorphicSection _ _
          (differenceSheafTensorPositiveIso D E).symm (canonicalMeromorphicSection D)
          (isRegularMeromorphicSection_canonicalMeromorphicSection D)).symm)

/-- The coefficient is the difference of the original full local quotient lengths. -/
@[colib_tag "COL-1050"]
theorem weilDivisorOfMeromorphicSection_canonicalDifference_apply
    [IsLocallyNoetherian X] (Z : AlgebraicGeometry.PrimeDivisor X) :
    (AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf D E)
      (canonicalDifferenceMeromorphicSection D E)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E)).val Z =
        effectiveCartierMultiplicity D Z - effectiveCartierMultiplicity E Z := by
  rw [weilDivisorOfMeromorphicSection_canonicalDifference_eq_sub]
  change AlgebraicGeometry.orderOfVanishingMeromorphic X _ _ _ Z -
    AlgebraicGeometry.orderOfVanishingMeromorphic X _ _ _ Z = _
  rw [orderOfVanishingMeromorphic_canonicalMeromorphicSection,
    orderOfVanishingMeromorphic_canonicalMeromorphicSection]

/-- The literal native Cartier Weil divisors occur with their original signs.
Global Noetherianness is precisely the hypothesis required by the native
`effectiveCartierWeilDivisor`; the coefficient statement only needs local Noetherianness. -/
@[colib_tag "COL-1050"]
theorem weilDivisorOfMeromorphicSection_canonicalDifference
    [IsNoetherian X] :
    AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf D E)
        (canonicalDifferenceMeromorphicSection D E)
        (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E) =
      effectiveCartierWeilDivisor D inferInstance -
        effectiveCartierWeilDivisor E inferInstance := by
  rw [weilDivisorOfMeromorphicSection_canonicalDifference_eq_sub,
    weilDivisorOfMeromorphicSection_canonicalMeromorphicSection,
    weilDivisorOfMeromorphicSection_canonicalMeromorphicSection]

end Stacks.Divisors
