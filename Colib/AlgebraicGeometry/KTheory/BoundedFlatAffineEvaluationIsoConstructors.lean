/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoherence

/-!
# Constructor equations for actual affine evaluation comparisons

These equalities retain the actual native isomorphisms as opaque endpoints of whole
coherence equations. They expose only their already chosen comparison constructors.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual native isomorphism is its specified comparison constructor. -/
theorem boundedAboveFlatAffineEvaluationModelIso_eq {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineEvaluationModelIso f =
      modelAsSmallEvaluationIso
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
        (boundedAboveFlatAffineSectionModelMap f) (boundedAboveFlatAffineEvaluationModelMap R)
        (boundedAboveFlatAffineEvaluationModelMap S) (boundedAboveFlatAffinePullbackModelMap f)
        (boundedAboveFlatAffineSectionsMap f) (boundedAboveFlatAffineOriginalEvaluation S)
        (boundedAboveFlatAffineOriginalEvaluation R) (boundedAboveFlatAffineNormalizedPullback f)
        (boundedAboveFlatAffineEvaluationCoefficientIso f)
        (boundedAboveFlatAffineEvaluationModelIso_source f)
        (boundedAboveFlatAffineEvaluationModelIso_target f) := rfl

/-- The actual native isomorphism is its specified comparison constructor. -/
theorem boundedAboveFlatAffinePullbackModelCompIso_eq {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffinePullbackModelCompIso f g =
      modelAsSmallCompositionIso
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
        (boundedAboveFlatAffineNormalizedPullback f)
        (boundedAboveFlatAffineNormalizedPullback g)
        (boundedAboveFlatAffineNormalizedPullback (f ≫ g))
        (boundedAboveFlatAffineNormalizedCompIso f g)
        (F₀ := (boundedAboveFlatAffinePullbackModelMap (f ≫ g)).hom.toFunctor)
        (G₀ := (boundedAboveFlatAffinePullbackModelMap f ≫
          boundedAboveFlatAffinePullbackModelMap g).hom.toFunctor)
        (boundedAboveFlatAffinePullbackModelMap_toFunctor (f ≫ g))
        (boundedAboveFlatAffinePullbackModelComp_toFunctor f g) := rfl

/-- The actual native isomorphism is its specified comparison constructor. -/
theorem boundedAboveFlatAffinePullbackModelIdIso_eq (R : CommRingCat.{u}) :
    boundedAboveFlatAffinePullbackModelIdIso R =
      modelAsSmallIdentityIso
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
        (boundedAboveFlatAffineNormalizedPullback (𝟙 R))
        (boundedAboveFlatAffineNormalizedIdIso R)
        (F₀ := (boundedAboveFlatAffinePullbackModelMap (𝟙 R)).hom.toFunctor)
        (G₀ := (𝟙 (asSmallCategory
          (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)) :
            asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) ⟶
              asSmallCategory
                (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).hom.toFunctor)
        (boundedAboveFlatAffinePullbackModelMap_toFunctor (𝟙 R))
        (smallModel_id_toFunctor
          (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))) := rfl

end AlgebraicGeometry.Scheme.Modules
