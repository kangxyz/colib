/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationZeroNormalization
import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPseudofunctor
import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback

/-!
# Actual affine consumers of generic section coherence

These formulas instantiate the sealed bounded-flat affine pseudofunctor, including
its actual Spec composition and identity transports. No Flat hypothesis, supplied
evaluation equivalence, strict affine spectrum row or derived/Bass theorem occurs.
The target normalizations are exactly rebasing at the actual Waldhausen zeros.
-/
noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
universe u
namespace ColibTest.AffineSectionTransitionCoherence
private abbrev affine : Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} :=
  boundedAboveFlatAffinePseudofunctor

/-- The generic forward equation keeps the original geometric constraint and Spec transport. -/
theorem affine_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (originalCoefficientIso affine (f ≫ g)).hom ≫
        whiskerLeft (originalEvaluation affine R)
          (eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≫
            (boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom) =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation affine T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget affine) f g)) ≫
          (originalCoefficientRouteIso affine f g).hom := by
  let K (μ : boundedAboveFlatPerfectPullback (Spec.map (f ≫ g)) ⟶
      boundedAboveFlatPerfectPullback (Spec.map f) ⋙
        boundedAboveFlatPerfectPullback (Spec.map g)) :=
    (originalCoefficientIso affine (f ≫ g)).hom ≫ whiskerLeft (originalEvaluation affine R) μ
  exact (congrArg K (boundedAboveFlatAffinePseudofunctor_mapComp_hom f g)).symm.trans
    (originalCoefficientIso_comp_hom affine f g)

/-- The actual affine identity comparison keeps Spec.map_id as well as coslice transport. -/
theorem affine_id (R : CommRingCat.{u}) :
    (originalCoefficientIso affine (𝟙 R)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation affine R)
          (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget affine) R)) ≫
        (Functor.leftUnitor (originalEvaluation affine R)).hom =
      whiskerLeft (originalEvaluation affine R)
        (eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_id R)) ≫
          (boundedAboveFlatPerfectPullbackIdIso (Spec R)).hom) ≫
        (Functor.rightUnitor (originalEvaluation affine R)).hom := by
  let K (ι : boundedAboveFlatPerfectPullback (Spec.map (𝟙 R)) ⟶
      𝟭 ((boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory)) :=
    whiskerLeft (originalEvaluation affine R) ι ≫
      (Functor.rightUnitor (originalEvaluation affine R)).hom
  exact (originalCoefficientIso_id affine R).trans
    (congrArg K (boundedAboveFlatAffinePseudofunctor_mapId_hom R))

/-- The actual functor rebased at the original Waldhausen zeros. -/
private def normalizedFunctor {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).FullSubcategory :=
  rebaseFunctor (boundedAboveFlatPerfectPullback (Spec.map f))
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).zero
    (((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).zero
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).isZero).iso
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).isZero)

/-- The exact original-functor-to-rebased-functor iso, with its target functor explicit. -/
private def normalization {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatPerfectPullback (Spec.map f) ≅ normalizedFunctor f :=
  rebaseFunctorIso (boundedAboveFlatPerfectPullback (Spec.map f))
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).zero
    (((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).zero
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).isZero).iso
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).isZero)

example {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (normalizedCoefficientIso affine (f ≫ g) (normalization (f ≫ g))).hom ≫
        whiskerLeft (originalEvaluation affine R)
          (normalizedCoefficientCompIso affine f g (normalization f)
            (normalization g) (normalization (f ≫ g))).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation affine T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget affine) f g)) ≫
          (normalizedCoefficientRouteIso affine f g (normalization f) (normalization g)).hom :=
  normalizedCoefficientIso_comp_hom affine f g _ _ _

/-- The geometric comparison has its actual Spec transport and explicit functor endpoints. -/
private def geometricComp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatPerfectPullback (Spec.map (f ≫ g)) ⟶
      boundedAboveFlatPerfectPullback (Spec.map f) ⋙
        boundedAboveFlatPerfectPullback (Spec.map g) :=
  eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≫
    (boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom

/-- The normalized constraint has explicit native functor endpoints. -/
private def normalizedComp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    normalizedFunctor (f ≫ g) ≅ normalizedFunctor f ⋙ normalizedFunctor g :=
  normalizedCoefficientCompIso affine f g (normalization f)
    (normalization g) (normalization (f ≫ g))

/-- Even after normalization the geometric composition retains its actual Spec transport. -/
example {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (normalizedComp f g).hom =
      (normalization (f ≫ g)).inv ≫
        geometricComp f g ≫
        whiskerRight (normalization f).hom (boundedAboveFlatPerfectPullback (Spec.map g)) ≫
        whiskerLeft (normalizedFunctor f) (normalization g).hom := by
  let K (μ : boundedAboveFlatPerfectPullback (Spec.map (f ≫ g)) ⟶
      boundedAboveFlatPerfectPullback (Spec.map f) ⋙
        boundedAboveFlatPerfectPullback (Spec.map g)) :=
    (normalization (f ≫ g)).inv ≫ μ ≫
      whiskerRight (normalization f).hom (boundedAboveFlatPerfectPullback (Spec.map g)) ≫
      whiskerLeft (normalizedFunctor f) (normalization g).hom
  exact (normalizedCoefficientCompIso_hom affine f g
    (normalization f) (normalization g) (normalization (f ≫ g))).trans
      (congrArg K (boundedAboveFlatAffinePseudofunctor_mapComp_hom f g))

example (R : CommRingCat.{u}) :
    (normalizedCoefficientIso affine (𝟙 R) (normalization (𝟙 R))).hom ≫
        whiskerLeft (originalEvaluation affine R)
          (normalizedCoefficientIdIso affine R (normalization (𝟙 R))).hom ≫
        (Functor.rightUnitor (originalEvaluation affine R)).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation affine R)
        (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget affine) R)) ≫
          (Functor.leftUnitor (originalEvaluation affine R)).hom :=
  normalizedCoefficientIso_id_hom affine R _

example (R : CommRingCat.{u}) :
    (normalizedCoefficientIdIso affine R (normalization (𝟙 R))).hom =
      (normalization (𝟙 R)).inv ≫
        eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_id R)) ≫
          (boundedAboveFlatPerfectPullbackIdIso (Spec R)).hom := by
  let K (ι : boundedAboveFlatPerfectPullback (Spec.map (𝟙 R)) ⟶
      𝟭 ((boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory)) :=
    (normalization (𝟙 R)).inv ≫ ι
  exact (normalizedCoefficientIdIso_hom affine R (normalization (𝟙 R))).trans
    (congrArg K (boundedAboveFlatAffinePseudofunctor_mapId_hom R))

-- Concrete composable nonidentity ring maps, not identity or a terminal-category substitute.
private def diagonal : CommRingCat.of ℤ ⟶ CommRingCat.of (ℤ × ℤ) :=
  CommRingCat.ofHom ((RingHom.id ℤ).prod (RingHom.id ℤ))

private def firstProjection : CommRingCat.of (ℤ × ℤ) ⟶ CommRingCat.of ℤ :=
  CommRingCat.ofHom (RingHom.fst ℤ ℤ)

example :
    (originalCoefficientIso affine (diagonal ≫ firstProjection)).hom ≫
        whiskerLeft (originalEvaluation affine (CommRingCat.of ℤ))
          (eqToHom (congrArg boundedAboveFlatPerfectPullback
            (Spec.map_comp diagonal firstProjection)) ≫
            (boundedAboveFlatPerfectPullbackCompIso
              (Spec.map firstProjection) (Spec.map diagonal)).hom) =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation affine (CommRingCat.of ℤ))
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget affine)
          diagonal firstProjection)) ≫
          (originalCoefficientRouteIso affine diagonal firstProjection).hom :=
  affine_comp diagonal firstProjection

end ColibTest.AffineSectionTransitionCoherence
