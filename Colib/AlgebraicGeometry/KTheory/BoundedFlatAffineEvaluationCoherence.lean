/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparisonIso
public import Colib.Topology.Prespectrum.RelativeHomotopyComposition
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Coherent normalized coefficient comparisons for affine evaluation

The composition and unit constraints are the original pseudofunctor constraints
conjugated by the same canonical zero normalizations. Their realization compares
whole tracks relatively, rather than claiming equality of concatenated paths.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.GrothendieckSections
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual composition of the canonically normalized geometric coefficient functors. -/
def boundedAboveFlatAffineNormalizedCompIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineNormalizedPullback (f ≫ g) ≅
      boundedAboveFlatAffineNormalizedPullback f ⋙ boundedAboveFlatAffineNormalizedPullback g :=
  normalizedCoefficientCompIso boundedAboveFlatAffinePseudofunctor f g
    (boundedAboveFlatAffinePullbackNormalization f)
    (boundedAboveFlatAffinePullbackNormalization g)
    (boundedAboveFlatAffinePullbackNormalization (f ≫ g))

/-- Actual unit of canonically normalized geometric coefficients. -/
def boundedAboveFlatAffineNormalizedIdIso (R : CommRingCat.{u}) :
    boundedAboveFlatAffineNormalizedPullback (𝟙 R) ≅
      𝟭 (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory :=
  normalizedCoefficientIdIso boundedAboveFlatAffinePseudofunctor R
    (boundedAboveFlatAffinePullbackNormalization (𝟙 R))

/-- The geometric composition comparison with its actual contravariant Spec transport. -/
def boundedAboveFlatAffineGeometricComp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatPerfectPullback (Spec.map (f ≫ g)) ⟶
      boundedAboveFlatPerfectPullback (Spec.map f) ⋙
        boundedAboveFlatPerfectPullback (Spec.map g) :=
  eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≫
    (boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom

/-- The named geometric comparison retains the exact original transport and comparison. -/
theorem boundedAboveFlatAffineGeometricComp_eq {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineGeometricComp f g =
      eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≫
        (boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom := rfl

/-- The actual composition constraint retains the contravariant Spec transport explicitly. -/
theorem boundedAboveFlatAffineNormalizedCompIso_hom
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineNormalizedCompIso f g).hom =
      (boundedAboveFlatAffinePullbackNormalization (f ≫ g)).inv ≫
        boundedAboveFlatAffineGeometricComp f g ≫
        whiskerRight (boundedAboveFlatAffinePullbackNormalization f).hom
          (boundedAboveFlatPerfectPullback (Spec.map g)) ≫
        whiskerLeft (boundedAboveFlatAffineNormalizedPullback f)
          (boundedAboveFlatAffinePullbackNormalization g).hom := by
  let K (μ : boundedAboveFlatPerfectPullback (Spec.map (f ≫ g)) ⟶
      boundedAboveFlatPerfectPullback (Spec.map f) ⋙
        boundedAboveFlatPerfectPullback (Spec.map g)) :=
    (boundedAboveFlatAffinePullbackNormalization (f ≫ g)).inv ≫ μ ≫
      whiskerRight (boundedAboveFlatAffinePullbackNormalization f).hom
        (boundedAboveFlatPerfectPullback (Spec.map g)) ≫
      whiskerLeft (boundedAboveFlatAffineNormalizedPullback f)
        (boundedAboveFlatAffinePullbackNormalization g).hom
  exact congrArg K (boundedAboveFlatAffinePseudofunctor_mapComp_hom f g)

/-- The actual unit constraint retains Spec.map_id rather than erasing its transport. -/
theorem boundedAboveFlatAffineNormalizedIdIso_hom (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineNormalizedIdIso R).hom =
      (boundedAboveFlatAffinePullbackNormalization (𝟙 R)).inv ≫
        eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_id R)) ≫
          (boundedAboveFlatPerfectPullbackIdIso (Spec R)).hom := by
  let K (ι : boundedAboveFlatPerfectPullback (Spec.map (𝟙 R)) ⟶
      𝟭 (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :=
    (boundedAboveFlatAffinePullbackNormalization (𝟙 R)).inv ≫ ι
  exact congrArg K (boundedAboveFlatAffinePseudofunctor_mapId_hom R)

/-- The composite model functor is identified by the proved original functor projections. -/
theorem boundedAboveFlatAffinePullbackModelComp_toFunctor {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffinePullbackModelMap f ≫
      boundedAboveFlatAffinePullbackModelMap g).hom.toFunctor =
        asSmallFunctor (boundedAboveFlatAffineNormalizedPullback f) ⋙
          asSmallFunctor (boundedAboveFlatAffineNormalizedPullback g) :=
  (smallModel_comp_toFunctor _ _).trans
    (congrArg₂
      (fun (F : AsSmall.{0}
          (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory ⥤
            AsSmall.{0} (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).FullSubcategory)
        (G : AsSmall.{0}
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).FullSubcategory ⥤
            AsSmall.{0} (boundedAboveFlatPerfectComplex (Spec T).toRingedSpace).FullSubcategory) =>
        F ⋙ G)
      (boundedAboveFlatAffinePullbackModelMap_toFunctor f)
      (boundedAboveFlatAffinePullbackModelMap_toFunctor g))

/-- The lifted composition constraint retains each original geometric component. -/
def boundedAboveFlatAffinePullbackModelCompIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffinePullbackModelMap (f ≫ g)).hom.toFunctor ≅
      (boundedAboveFlatAffinePullbackModelMap f ≫
        boundedAboveFlatAffinePullbackModelMap g).hom.toFunctor := by
  exact modelAsSmallCompositionIso
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
    (boundedAboveFlatAffinePullbackModelComp_toFunctor f g)

/-- The lifted unit constraint retains the original geometric unit component. -/
def boundedAboveFlatAffinePullbackModelIdIso (R : CommRingCat.{u}) :
    (boundedAboveFlatAffinePullbackModelMap (𝟙 R)).hom.toFunctor ≅
      (𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)) :
        asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) ⟶
          asSmallCategory
            (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).hom.toFunctor := by
  exact modelAsSmallIdentityIso
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
      (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)))

/-- The actual normalized coefficient composition track. -/
def boundedAboveFlatAffinePullbackCompHomotopy {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map (f ≫ g)))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map g)) :=
  (prespectrumTransformationHomotopy
    (F := boundedAboveFlatAffinePullbackModelMap (f ≫ g))
    (G := boundedAboveFlatAffinePullbackModelMap f ≫ boundedAboveFlatAffinePullbackModelMap g)
    (boundedAboveFlatAffinePullbackModelCompIso f g).hom
    (fun x => (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace).asSmall.weq_iso _ (by
      change IsIso ((boundedAboveFlatAffinePullbackModelCompIso f g).hom.app x)
      infer_instance))).cast rfl (prespectrumFunctor.map_comp _ _)

/-- The actual normalized coefficient unit track. -/
def boundedAboveFlatAffinePullbackIdHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map (𝟙 R)))
      (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))) :=
  (prespectrumTransformationHomotopy
    (F := boundedAboveFlatAffinePullbackModelMap (𝟙 R))
    (G := 𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)))
    (boundedAboveFlatAffinePullbackModelIdIso R).hom
    (fun x => (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).asSmall.weq_iso _ (by
      change IsIso ((boundedAboveFlatAffinePullbackModelIdIso R).hom.app x)
      infer_instance))).cast rfl (prespectrumFunctor.map_id _)

/-- The normalized two-arrow route retains all original categorical associators. -/
def boundedAboveFlatAffineEvaluationRouteIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineSectionsMap g) ⋙
        boundedAboveFlatAffineOriginalEvaluation T ≅
      boundedAboveFlatAffineOriginalEvaluation R ⋙ boundedAboveFlatAffineNormalizedPullback f ⋙
        boundedAboveFlatAffineNormalizedPullback g :=
  normalizedCoefficientRouteIso boundedAboveFlatAffinePseudofunctor f g
    (boundedAboveFlatAffinePullbackNormalization f) (boundedAboveFlatAffinePullbackNormalization g)

/-- The complete normalized coefficient equation comes from actual section transitions. -/
theorem boundedAboveFlatAffineEvaluationCoefficientIso_comp_hom
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationCoefficientIso (f ≫ g)).hom ≫
        whiskerLeft (boundedAboveFlatAffineOriginalEvaluation R)
          (boundedAboveFlatAffineNormalizedCompIso f g).hom =
      eqToHom (congrArg (fun G => G ⋙ boundedAboveFlatAffineOriginalEvaluation T)
        (boundedAboveFlatAffineSectionsMap_comp f g)) ≫
          (boundedAboveFlatAffineEvaluationRouteIso f g).hom :=
  normalizedCoefficientIso_comp_hom boundedAboveFlatAffinePseudofunctor f g
    (boundedAboveFlatAffinePullbackNormalization f) (boundedAboveFlatAffinePullbackNormalization g)
    (boundedAboveFlatAffinePullbackNormalization (f ≫ g))

/-- The normalized unit retains the strict source transport and original target unit. -/
theorem boundedAboveFlatAffineEvaluationCoefficientIso_id_hom (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineEvaluationCoefficientIso (𝟙 R)).hom ≫
        whiskerLeft (boundedAboveFlatAffineOriginalEvaluation R)
          (boundedAboveFlatAffineNormalizedIdIso R).hom ≫
        (Functor.rightUnitor (boundedAboveFlatAffineOriginalEvaluation R)).hom =
      eqToHom (congrArg (fun G => G ⋙ boundedAboveFlatAffineOriginalEvaluation R)
        (boundedAboveFlatAffineSectionsMap_id R)) ≫
          (Functor.leftUnitor (boundedAboveFlatAffineOriginalEvaluation R)).hom :=
  normalizedCoefficientIso_id_hom boundedAboveFlatAffinePseudofunctor R
    (boundedAboveFlatAffinePullbackNormalization (𝟙 R))

end AlgebraicGeometry.Scheme.Modules
