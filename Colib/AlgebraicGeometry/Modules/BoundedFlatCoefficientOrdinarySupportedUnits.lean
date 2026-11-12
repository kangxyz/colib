/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportModels
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionUnits
/-! # Original ordinary supported forward coefficient units

These four original declarations specialize the existing support inclusion to the ordinary
coefficient row. The literal unit and its full coefficient-preservation equation are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

/-- The original joint section unit restricted through the actual supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportUnits.lean:38"
  "adaptation" "Original supported coefficient unit and actual forward Laurent preservation"]
def boundedAboveFlatCoefficientSupportedUnitIso (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    𝟭 ((boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).FullSubcategory) ≅ 𝟭
      ((boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).FullSubcategory) :=
  lift (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedAboveFlatCoefficientSectionUnitIso (op Q, a) (boundedAboveFlatCoefficientUnit (op Q,
      a) r))

/-- Forgetting support keeps precisely the original forward unit component. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportUnits.lean:44"
  "adaptation" "Original supported coefficient unit and actual forward Laurent preservation"]
theorem boundedAboveFlatCoefficientSupportedUnitIso_hom
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) (S : (boundedAboveFlatCoefficientSectionSupported
      (schemeMap f a)).FullSubcategory) :
    ((boundedAboveFlatCoefficientSupportedUnitIso f a r).hom.app S).hom =
      (boundedAboveFlatCoefficientSectionUnitIso (op Q, a)
        (boundedAboveFlatCoefficientUnit (op Q, a) r)).hom.app S.obj :=
  map_lift_hom (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι _ S

/-- The actual forward Laurent coordinate on the original supported coefficient fiber. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportUnits.lean:52"
  "adaptation" "Original supported coefficient unit and actual forward Laurent preservation"]
def boundedAboveFlatCoefficientSupportedLaurentUnitIso (a : Under R) :=
  boundedAboveFlatCoefficientSupportedUnitIso f ((laurentUnderFunctor R).obj a)
    (laurentCoordinate a.right)

/-- Actual supported coefficient reindexing preserves the same native forward Laurent unit. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportUnits.lean:57"
  "adaptation" "Original supported coefficient unit and actual forward Laurent preservation"]
theorem boundedAboveFlatCoefficientSupportedLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedAboveFlatCoefficientSupportedModelFunctor f).map
      ((laurentUnderFunctor R).map g)).hom.toFunctor
      (boundedAboveFlatCoefficientSupportedLaurentUnitIso f a)
      (boundedAboveFlatCoefficientSupportedLaurentUnitIso f b) := by
  change Preserves (boundedAboveFlatCoefficientSupportedSectionsMap
    (schemeMap f ((laurentUnderFunctor R).obj a)) (schemeMap f ((laurentUnderFunctor R).obj b))
    (i := (op Q, (laurentUnderFunctor R).obj a))
    (k := (op Q, (laurentUnderFunctor R).obj b))
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedAboveFlatCoefficientOpenPairMap f ((laurentUnderFunctor R).map g)).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenPairMap f ((laurentUnderFunctor
      R).map g)))) _ _
  intro S
  apply ObjectProperty.hom_ext
  change (boundedAboveFlatCoefficientSectionsMap
    (i := (op Q, (laurentUnderFunctor R).obj a))
    (k := (op Q, (laurentUnderFunctor R).obj b))
    (𝟙 (op Q), (laurentUnderFunctor R).map g)).map
      ((boundedAboveFlatCoefficientSupportedLaurentUnitIso f a).hom.app S).hom = _
  dsimp only [boundedAboveFlatCoefficientSupportedLaurentUnitIso]
  rw [boundedAboveFlatCoefficientSupportedUnitIso_hom,
    boundedAboveFlatCoefficientSupportedUnitIso_hom]
  simpa only [boundedAboveFlatCoefficientSectionLaurentUnitIso,
    boundedAboveFlatCoefficientSupportedSectionsMap, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj] using
      boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient Q g S.obj

end AlgebraicGeometry.Scheme.Modules
