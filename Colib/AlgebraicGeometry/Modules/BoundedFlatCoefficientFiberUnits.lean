/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedUnits
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientFiberInclusion
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenModels

/-!
# Actual units with the original intersection support

The lifted forward Laurent unit and actual supported coefficient/inclusion maps retain their
original identity-automorphism preservation equations.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

/-- The original forward Laurent unit on the actual intersection-support native fiber. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberUnits.lean:38"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso (a : Under R) :=
  lift (boundedAboveFlatCoefficientSectionSupported
    (boundedAboveFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedAboveFlatCoefficientSectionLaurentUnitIso Q a)

/-- Actual coefficient reindexing preserves every original forward fiber-unit component. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberUnits.lean:68"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedAboveFlatCoefficientSupportedFiberModelFunctor f T).map
      ((laurentUnderFunctor R).map g)).hom.toFunctor
      (boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T a)
      (boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T b) :=
  supportMap_preserves_lift
    (boundedAboveFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (boundedAboveFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedAboveFlatCoefficientFiberSupportPairMap f T ((laurentUnderFunctor R).map g)).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientFiberSupportPairMap f T
      ((laurentUnderFunctor R).map g)))
    _ _ (boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient Q g)

/-- Forgetting extra support retains every actual forward unit component. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientFiberUnits.lean:82"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem supportedFiberForget_unit_preserves (a : Under R)
    (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSupportedFiberForget f T a)
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
        r)
      (boundedAboveFlatCoefficientSupportSectionUnitIso (boundedAboveFlatCoefficientSupportOpen Q
        T a).ι r) :=
        by
  intro S
  apply ObjectProperty.hom_ext
  change ((boundedAboveFlatCoefficientSupportSectionUnitIso
    (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι r).hom.app S).hom =
    ((boundedAboveFlatCoefficientSupportSectionUnitIso
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι r).hom.app
      ((boundedAboveFlatCoefficientSupportedFiberForget f T a).obj S)).hom
  rw [boundedAboveFlatCoefficientSupportSectionUnitIso_hom,
    boundedAboveFlatCoefficientSupportSectionUnitIso_hom]
  rfl

end AlgebraicGeometry.Scheme.Modules
