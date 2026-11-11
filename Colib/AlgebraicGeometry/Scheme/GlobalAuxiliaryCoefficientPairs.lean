/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.GlobalAuxiliaryParameterCoefficientGeometry
public import Colib.AlgebraicGeometry.Scheme.GlobalSupportedCoefficientGeometry


/-!
# The original auxiliary support pairs and their integral row comparison

The support inclusion over the integer base is base changed using the original coefficient
construction. Its actual open range is the old auxiliary support open. The resulting pair
isomorphism retains the ambient identity and then the original canonical row symmetry.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient

variable {R : CommRingCat.{u}} (Q : Over (Spec R)) (T : Q.left.Opens)

/-- The actual support open with its original structure map to the coefficient base. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:32"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
def supportObject : Over (Spec R) := Over.mk (T.ι ≫ Q.hom)

/-- The original support inclusion as a morphism over the base. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:35"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
def supportArrow : supportObject Q T ⟶ Q := Over.homMk T.ι rfl

/-- The original support inclusion is still the given open immersion over the base. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:38"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
instance supportArrow_isOpenImmersion : IsOpenImmersion (supportArrow Q T).left :=
  inferInstanceAs (IsOpenImmersion T.ι)

/-- Base change of the actual support inclusion has precisely the old support open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:42"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
theorem supportArrow_range (a : Under R) :
    (schemeMap (supportArrow Q T) a).opensRange =
      boundedAboveFlatCoefficientSupportOpen Q T a := by
  rw [← AlgebraicGeometry.preimage_opensRange_of_isPullback
    (schemeMap_isPullback (supportArrow Q T) a)]
  change projection (op Q, a) ⁻¹ᵁ T.ι.opensRange = _
  rw [Scheme.Opens.opensRange_ι]
  rfl

/-- The old support-open scheme is the actual open range of the base-changed inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:53"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
def supportRangeIso (a : Under R) :
    ((boundedAboveFlatCoefficientSupportOpen Q T a) : Scheme.{u}) ≅ space (op (supportObject Q T),
      a) :=
  IsOpenImmersion.isoOfRangeEq (boundedAboveFlatCoefficientSupportOpen Q T a).ι
    (schemeMap (supportArrow Q T) a) (by
      change ((boundedAboveFlatCoefficientSupportOpen Q T a).ι.opensRange : Set (space (op Q, a))) =
        ((schemeMap (supportArrow Q T) a).opensRange : Set (space (op Q, a)))
      rw [Scheme.Opens.opensRange_ι, supportArrow_range])

/-- The range identification retains the original support inclusion itself. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:62"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
theorem supportRangeIso_fac (a : Under R) :
    (supportRangeIso Q T a).hom ≫ schemeMap (supportArrow Q T) a =
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The old support pair and base-changed original support arrow are genuinely isomorphic. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:68"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
def supportPairIso (a : Under R) :
    supportOpenPair (boundedAboveFlatCoefficientSupportOpen Q T a) ≅
      boundedAboveFlatCoefficientOpenPair (supportArrow Q T) a :=
  MorphismProperty.Arrow.isoMk (supportRangeIso Q T a) (Iso.refl _) (by
      change (supportRangeIso Q T a).hom ≫ schemeMap (supportArrow Q T) a =
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι ≫ 𝟙 _
      rw [Category.comp_id]
      exact supportRangeIso_fac Q T a)

/-- The ambient corner of this pair comparison is literally the identity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:79"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
theorem supportPairIso_hom_right (a : Under R) :
    (supportPairIso Q T a).hom.right = 𝟙 _ := rfl

variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)

/-- The old native auxiliary support pair maps to the unchanged parameter support pair. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:85"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
def parameterSupportPairIso (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    supportOpenPair (boundedAboveFlatCoefficientSupportOpen Q T a) ≅
      GlobalSupportedParameter.pair T.ι (Spec a.right) :=
  supportPairIso Q T a ≪≫ GlobalSupportedParameter.coefficientPairIso (supportArrow Q T) a

/-- The whole pair comparison uses exactly the prescribed ambient row symmetry. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalAuxiliaryCoefficientPairs.lean:91"
  "adaptation" "Actual integral auxiliary support opens and complete support-pair symmetry"]
theorem parameterSupportPairIso_hom_right
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterSupportPairIso Q T a).hom.right = (canonicalRowIso Q a).hom := by
  change 𝟙 _ ≫ (canonicalRowIso Q a).hom = _
  exact Category.id_comp _

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
