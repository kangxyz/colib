/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoherence

/-!
# Explicit components of actual affine evaluation comparisons

The actual coefficient and route components are exposed before they are lifted to model
coherence. All original section transports and geometric normalizations are retained.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules


/-- The two original normalized comparisons retain their explicit associators. -/
theorem boundedAboveFlatAffineEvaluationRouteIso_hom
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationRouteIso f g).hom =
      (Functor.associator (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineSectionsMap g) (boundedAboveFlatAffineOriginalEvaluation T)).hom ≫
      whiskerLeft (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineEvaluationCoefficientIso g).hom ≫
      (Functor.associator (boundedAboveFlatAffineSectionsMap f)
        (boundedAboveFlatAffineOriginalEvaluation S)
        (boundedAboveFlatAffineNormalizedPullback g)).inv ≫
      whiskerRight (boundedAboveFlatAffineEvaluationCoefficientIso f).hom
        (boundedAboveFlatAffineNormalizedPullback g) ≫
      (Functor.associator (boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatAffineNormalizedPullback f)
        (boundedAboveFlatAffineNormalizedPullback g)).hom := by
  unfold boundedAboveFlatAffineEvaluationRouteIso
    boundedAboveFlatAffineEvaluationCoefficientIso boundedAboveFlatAffineSectionsMap
    boundedAboveFlatAffineOriginalEvaluation boundedAboveFlatAffineProjection
  simp only [CategoryTheory.GrothendieckSections.normalizedCoefficientRouteIso,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom]
  congr 4

/-- The normalized route has precisely the original two coefficient components. -/
theorem boundedAboveFlatAffineEvaluationRouteIso_hom_app
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineEvaluationRouteIso f g).hom.app s =
      (boundedAboveFlatAffineEvaluationCoefficientIso g).hom.app
        ((boundedAboveFlatAffineSectionsMap f).obj s) ≫
      (boundedAboveFlatAffineNormalizedPullback g).map
        ((boundedAboveFlatAffineEvaluationCoefficientIso f).hom.app s) := by
  rw [boundedAboveFlatAffineEvaluationRouteIso_hom]
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]


/-- The original normalized composition equation evaluated at an actual section. -/
theorem boundedAboveFlatAffineEvaluationCoefficientIso_comp_app
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineEvaluationCoefficientIso (f ≫ g)).hom.app s ≫
        (boundedAboveFlatAffineNormalizedCompIso f g).hom.app
          ((boundedAboveFlatAffineOriginalEvaluation R).obj s) =
      (eqToHom (congrArg (fun G => G ⋙ boundedAboveFlatAffineOriginalEvaluation T)
        (boundedAboveFlatAffineSectionsMap_comp f g))).app s ≫
        (boundedAboveFlatAffineEvaluationCoefficientIso g).hom.app
          ((boundedAboveFlatAffineSectionsMap f).obj s) ≫
        (boundedAboveFlatAffineNormalizedPullback g).map
          ((boundedAboveFlatAffineEvaluationCoefficientIso f).hom.app s) := by
  have h := congrArg (fun η :
      boundedAboveFlatAffineSectionsMap (f ≫ g) ⋙ boundedAboveFlatAffineOriginalEvaluation T ⟶
        boundedAboveFlatAffineOriginalEvaluation R ⋙ boundedAboveFlatAffineNormalizedPullback f ⋙
          boundedAboveFlatAffineNormalizedPullback g => η.app s)
    (boundedAboveFlatAffineEvaluationCoefficientIso_comp_hom f g)
  simpa only [NatTrans.comp_app, whiskerLeft_app,
    boundedAboveFlatAffineEvaluationRouteIso_hom_app] using h

/-- The original normalized unit equation evaluated at an actual section. -/
theorem boundedAboveFlatAffineEvaluationCoefficientIso_id_app (R : CommRingCat.{u})
    (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineEvaluationCoefficientIso (𝟙 R)).hom.app s ≫
        (boundedAboveFlatAffineNormalizedIdIso R).hom.app
          ((boundedAboveFlatAffineOriginalEvaluation R).obj s) =
      (eqToHom (congrArg (fun G => G ⋙ boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatAffineSectionsMap_id R))).app s := by
  have h := congrArg (fun η :
      boundedAboveFlatAffineSectionsMap (𝟙 R) ⋙ boundedAboveFlatAffineOriginalEvaluation R ⟶
        boundedAboveFlatAffineOriginalEvaluation R => η.app s)
    (boundedAboveFlatAffineEvaluationCoefficientIso_id_hom R)
  let a := (boundedAboveFlatAffineEvaluationCoefficientIso (𝟙 R)).hom.app s
  let b := (boundedAboveFlatAffineNormalizedIdIso R).hom.app
    ((boundedAboveFlatAffineOriginalEvaluation R).obj s)
  let e := (eqToHom (congrArg (fun G => G ⋙ boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatAffineSectionsMap_id R))).app s
  have h' : a ≫ b ≫ 𝟙 ((boundedAboveFlatAffineOriginalEvaluation R).obj s) =
      e ≫ 𝟙 ((boundedAboveFlatAffineOriginalEvaluation R).obj s) := by
    simpa only [a, b, e, NatTrans.comp_app, whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] using h
  exact (Category.comp_id (a ≫ b)).symm.trans
    ((Category.assoc a b (𝟙 _)).trans (h'.trans (Category.comp_id e)))


end AlgebraicGeometry.Scheme.Modules
