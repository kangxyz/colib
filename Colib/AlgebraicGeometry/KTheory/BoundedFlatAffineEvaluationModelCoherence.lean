/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationRawSource
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationIsoConstructors
public import Colib.KTheory.Waldhausen.Iterated.SmallSourceEvaluationComparison

/-!
# Actual whole affine evaluation composition and unit equations
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

local notation "A" => boundedAboveFlatAffineSectionModelMap
local notation "E" => boundedAboveFlatAffineEvaluationModelMap
local notation "P" => boundedAboveFlatAffinePullbackModelMap
local notation "α" => boundedAboveFlatAffineEvaluationModelIso
local notation "μ" => boundedAboveFlatAffinePullbackModelCompIso
local notation "δ" => boundedAboveFlatAffinePullbackModelIdIso

/-- The source bridge is exactly the existing native section model, including its zero. -/
theorem boundedAboveFlatAffineSectionModel_eq_smallSourceModel (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionModel R =
      smallSourceModel (boundedAboveFlatAffineSectionWaldhausen R) := rfl

/-- The actual strict source-row composition, with its original association. -/
theorem boundedAboveFlatAffineEvaluationModelCompSource
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    A (f ≫ g) ≫ E T = A f ≫ (A g ≫ E T) :=
  (congrArg (fun k : boundedAboveFlatAffineSectionModel R ⟶
      boundedAboveFlatAffineSectionModel T => k ≫ E T)
    (boundedAboveFlatAffineSectionModelFunctor.map_comp f g)).trans (Category.assoc _ _ _)

/-- The actual strict source-row unit, before applying the prespectrum construction. -/
theorem boundedAboveFlatAffineEvaluationModelIdSource (R : CommRingCat.{u}) :
    A (𝟙 R) ≫ E R = E R :=
  (congrArg (fun k : boundedAboveFlatAffineSectionModel R ⟶
      boundedAboveFlatAffineSectionModel R => k ≫ E R)
    (boundedAboveFlatAffineSectionModelFunctor.map_id R)).trans (Category.id_comp _)

/-- Specialization of the actual generic native composition theorem. -/
private abbrev affineEvaluationCompSpecialization
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :=
  smallSourceEvaluationIso_comp_hom
    (C₀ := BoundedAboveFlatAffineSections R)
    (C₁ := BoundedAboveFlatAffineSections S)
    (C₂ := BoundedAboveFlatAffineSections T)
    (boundedAboveFlatAffineSectionWaldhausen R)
    (boundedAboveFlatAffineSectionWaldhausen S)
    (boundedAboveFlatAffineSectionWaldhausen T)
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
    (A f) (A g) (A (f ≫ g)) (E R) (E S) (E T) (P f) (P g) (P (f ≫ g))
    (boundedAboveFlatAffineSectionsMap f) (boundedAboveFlatAffineSectionsMap g)
    (boundedAboveFlatAffineSectionsMap (f ≫ g))
    (boundedAboveFlatAffineOriginalEvaluation R) (boundedAboveFlatAffineOriginalEvaluation S)
    (boundedAboveFlatAffineOriginalEvaluation T)
    (boundedAboveFlatAffineNormalizedPullback f) (boundedAboveFlatAffineNormalizedPullback g)
    (boundedAboveFlatAffineNormalizedPullback (f ≫ g))
    (boundedAboveFlatAffineEvaluationCoefficientIso f)
    (boundedAboveFlatAffineEvaluationCoefficientIso g)
    (boundedAboveFlatAffineEvaluationCoefficientIso (f ≫ g))
    (boundedAboveFlatAffineNormalizedCompIso f g)
    (boundedAboveFlatAffineSectionModelMap_toFunctor f)
    (boundedAboveFlatAffineSectionModelMap_toFunctor g)
    (boundedAboveFlatAffineSectionModelMap_toFunctor (f ≫ g))
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor R)
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor S)
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor T)
    (boundedAboveFlatAffinePullbackModelMap_toFunctor f)
    (boundedAboveFlatAffinePullbackModelMap_toFunctor g)
    (boundedAboveFlatAffinePullbackModelMap_toFunctor (f ≫ g))
    (boundedAboveFlatAffinePullbackModelComp_toFunctor f g)
    (boundedAboveFlatAffineEvaluationModelIso_source f)
    (boundedAboveFlatAffineEvaluationModelIso_target f)
    (boundedAboveFlatAffineEvaluationModelIso_source g)
    (boundedAboveFlatAffineEvaluationModelIso_target g)
    (boundedAboveFlatAffineEvaluationModelIso_source (f ≫ g))
    (boundedAboveFlatAffineEvaluationModelIso_target (f ≫ g))
    (boundedAboveFlatAffineEvaluationRawCompSource f g)
    (boundedAboveFlatAffineEvaluationModelCompSource f g)

/-- Specialization with the proved actual raw composition premise. -/
private abbrev affineEvaluationCompRaw
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :=
  affineEvaluationCompSpecialization f g (boundedAboveFlatAffineEvaluationRawComp_app f g)

/-- Apply the unchanged actual native comparisons and their proved constructor identities. -/
private abbrev affineEvaluationCompWhole
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :=
  affineEvaluationCompRaw f g (α f) (α g) (α (f ≫ g)) (μ f g)
    (boundedAboveFlatAffineEvaluationModelIso_eq f)
    (boundedAboveFlatAffineEvaluationModelIso_eq g)
    (boundedAboveFlatAffineEvaluationModelIso_eq (f ≫ g))
    (boundedAboveFlatAffinePullbackModelCompIso_eq f g)

/-- The original public native composition equation, with unchanged actual comparisons. -/
theorem boundedAboveFlatAffineEvaluationModelIso_comp_hom
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (α (f ≫ g)).hom ≫ modelWhiskerLeft (E R) (μ f g).hom =
      modelEqToHom (boundedAboveFlatAffineEvaluationModelCompSource f g) ≫
        modelWhiskerLeft (A f) (α g).hom ≫
          modelWhiskerRightAssoc (A f) (E S) (E R) (P f) (P g) (α f).hom :=
  affineEvaluationCompWhole f g

/-- Specialize unit coherence with the unchanged raw identity source transport. -/
private abbrev affineEvaluationUnitSpecialization (R : CommRingCat.{u}) :=
  smallSourceEvaluationIso_id_hom
    (C₀ := BoundedAboveFlatAffineSections R)
    (boundedAboveFlatAffineSectionWaldhausen R)
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
    (A (𝟙 R)) (E R) (P (𝟙 R))
    (boundedAboveFlatAffineSectionsMap (𝟙 R)) (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatAffineNormalizedPullback (𝟙 R))
    (boundedAboveFlatAffineEvaluationCoefficientIso (𝟙 R))
    (boundedAboveFlatAffineNormalizedIdIso R)
    (boundedAboveFlatAffineSectionModelMap_toFunctor (𝟙 R))
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor R)
    (boundedAboveFlatAffinePullbackModelMap_toFunctor (𝟙 R))
    (boundedAboveFlatAffineEvaluationModelIso_source (𝟙 R))
    (boundedAboveFlatAffineEvaluationModelIso_target (𝟙 R))
    (congrArg (fun G => G ⋙ boundedAboveFlatAffineOriginalEvaluation R)
      (boundedAboveFlatAffineSectionsMap_id R))
    (boundedAboveFlatAffineEvaluationModelIdSource R)

/-- Supply the original actual raw unit component equation. -/
private abbrev affineEvaluationUnitRaw (R : CommRingCat.{u}) :=
  affineEvaluationUnitSpecialization R (boundedAboveFlatAffineEvaluationCoefficientIso_id_app R)

/-- Supply the actual identity coefficient comparisons and their constructor equalities. -/
private abbrev affineEvaluationUnitWhole (R : CommRingCat.{u}) :=
  affineEvaluationUnitRaw R (α (𝟙 R)) (δ R)
    (boundedAboveFlatAffineEvaluationModelIso_eq (𝟙 R))
    (boundedAboveFlatAffinePullbackModelIdIso_eq R)

/-- The original public native unit equation. -/
theorem boundedAboveFlatAffineEvaluationModelIso_id_hom (R : CommRingCat.{u}) :
    (α (𝟙 R)).hom ≫ modelWhiskerLeftId (E R) (δ R).hom =
      modelEqToHom (boundedAboveFlatAffineEvaluationModelIdSource R) :=
  affineEvaluationUnitWhole R

end AlgebraicGeometry.Scheme.Modules
