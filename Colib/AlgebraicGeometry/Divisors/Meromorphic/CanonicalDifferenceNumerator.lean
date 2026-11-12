/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifference
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.GlobalSectionTransport

/-!
# The ordinary numerator of the canonical Cartier-difference section

The canonical numerator is an ordinary section transported through the actual
Cartier evaluation isomorphism. Its meromorphic image is the numerator already
used to construct the canonical difference section. Thus regular tensor division
can be applied on the original denominator's nonvanishing open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

local instance numeratorDifferenceInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (differenceSheaf D E) :=
  (isInvertible_differenceSheaf D E).toAlgebraicGeometry

local instance numeratorQuasicoherent (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    L.IsQuasicoherent := isQuasicoherent_of_isInvertible L

local instance numeratorTensorQuasicoherent :
    (Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E)).IsQuasicoherent :=
  (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (differenceSheafTensorPositiveIso D E).symm inferInstance

/-- The original canonical section of `𝒪(D)` transported as an ordinary global section. -/
def canonicalDifferenceGlobalNumerator :
    Γ(Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E), ⊤) :=
  (differenceSheafTensorPositiveIso D E).inv.app ⊤ (divisorSheafGlobalSection D)

/-- The ordinary transported numerator has precisely the meromorphic image used in the
canonical difference construction. -/
theorem meromorphicSectionOfGlobalSection_canonicalDifferenceGlobalNumerator [IsIntegral X] :
    meromorphicSectionOfGlobalSection _ (canonicalDifferenceGlobalNumerator D E) =
      canonicalDifferenceNumerator D E :=
  meromorphicSectionOfGlobalSection_map _ _ (differenceSheafTensorPositiveIso D E).inv _

/-- On an integral scheme the original ordinary numerator is nonzero. -/
theorem canonicalDifferenceGlobalNumerator_ne_zero [IsIntegral X] :
    canonicalDifferenceGlobalNumerator D E ≠ 0 := by
  have hs := globalSection_ne_zero_of_isRegularSection _ _ (canonicalSection_isRegular D)
  intro h
  apply hs
  exact injective_iso_hom_val_app (differenceSheafTensorPositiveIso D E).symm _
    (h.trans (map_zero _).symm)

end Stacks.Divisors
