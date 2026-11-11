/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationComparison
public import Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationCoherence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumPullback
public import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationZeroNormalization
/-!
# Actual coefficient tracks for affine section evaluation
The original section transition is followed by the same canonical chosen-zero rebasing
used by the geometric prespectrum map. Only then is it lifted through AsSmall. Every ring
map is allowed; exact termwise perfect pullback is a separate, flat-only comparison.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.GrothendieckSections
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
/-- Geometric pullback rebased at its actual original Waldhausen zeros. -/
def boundedAboveFlatAffineNormalizedPullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).FullSubcategory :=
  CategoryTheory.rebaseFunctor (boundedAboveFlatPerfectPullback (Spec.map f))
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).zero
    (((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).zero
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).isZero).iso
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).isZero)
/-- The actual natural isomorphism to the canonical normalization. -/
def boundedAboveFlatAffinePullbackNormalization {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatPerfectPullback (Spec.map f) ≅ boundedAboveFlatAffineNormalizedPullback f :=
  CategoryTheory.rebaseFunctorIso (boundedAboveFlatPerfectPullback (Spec.map f))
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).zero
    (((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).zero
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).isZero).iso
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).isZero)
/-- The actual evaluation transition followed by the specified pullback normalization. -/
def boundedAboveFlatAffineEvaluationCoefficientIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S ≅
      boundedAboveFlatAffineOriginalEvaluation R ⋙ boundedAboveFlatAffineNormalizedPullback f :=
  normalizedCoefficientIso boundedAboveFlatAffinePseudofunctor f
    (boundedAboveFlatAffinePullbackNormalization f)
/-- The coefficient model arrow uses exactly the normalization in geometric spectrum pullback. -/
def boundedAboveFlatAffinePullbackModelMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace) :=
  asSmallCategoryMap _ _ (boundedAboveFlatPerfectPullback_isExact (Spec.map f)).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
/-- No new geometric spectrum arrow is substituted for the original canonical one. -/
theorem boundedAboveFlatAffinePullbackModelMap_prespectrum {R S : CommRingCat.{u}} (f : R ⟶ S) :
    prespectrumMap (boundedAboveFlatAffinePullbackModelMap f) =
      boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f) := rfl
/-- The evaluation model retains the explicit lifted geometric functor. -/
theorem boundedAboveFlatAffineEvaluationModelMap_toFunctor (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineEvaluationModelMap R).hom.toFunctor =
      boundedAboveFlatAffineOriginalEvaluation R ⋙ AsSmall.up := rfl
/-- The coefficient model retains the explicit normalized geometric functor. -/
theorem boundedAboveFlatAffinePullbackModelMap_toFunctor {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffinePullbackModelMap f).hom.toFunctor =
      asSmallFunctor (boundedAboveFlatAffineNormalizedPullback f) := rfl
/-- The actual source functor projection for the lifted evaluation comparison. -/
theorem boundedAboveFlatAffineEvaluationModelIso_source {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionModelMap f ≫
      boundedAboveFlatAffineEvaluationModelMap S).hom.toFunctor =
        boundedAboveFlatAffineSectionsMap f ⋙
          (boundedAboveFlatAffineOriginalEvaluation S ⋙ AsSmall.up) :=
  modelEvaluationSource_toFunctor
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
    (boundedAboveFlatAffineSectionModelMap f) (boundedAboveFlatAffineEvaluationModelMap S)
    (boundedAboveFlatAffineSectionsMap f) (boundedAboveFlatAffineOriginalEvaluation S)
    (boundedAboveFlatAffineSectionModelMap_toFunctor f)
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor S)
/-- The actual target functor projection, retaining canonical chosen-zero normalization. -/
theorem boundedAboveFlatAffineEvaluationModelIso_target {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineEvaluationModelMap R ≫
      boundedAboveFlatAffinePullbackModelMap f).hom.toFunctor =
        (boundedAboveFlatAffineOriginalEvaluation R ⋙ AsSmall.up) ⋙
          asSmallFunctor (boundedAboveFlatAffineNormalizedPullback f) :=
  modelEvaluationTarget_toFunctor
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
    (boundedAboveFlatAffineEvaluationModelMap R) (boundedAboveFlatAffinePullbackModelMap f)
    (boundedAboveFlatAffineOriginalEvaluation R) (boundedAboveFlatAffineNormalizedPullback f)
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor R)
    (boundedAboveFlatAffinePullbackModelMap_toFunctor f)
/-- The original transition comparison, with explicit native-model endpoint transports. -/
def boundedAboveFlatAffineEvaluationModelIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionModelMap f ≫
        boundedAboveFlatAffineEvaluationModelMap S).hom.toFunctor ≅
      (boundedAboveFlatAffineEvaluationModelMap R ≫
        boundedAboveFlatAffinePullbackModelMap f).hom.toFunctor :=
  modelAsSmallEvaluationIso
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
    (boundedAboveFlatAffineSectionModelMap f) (boundedAboveFlatAffineEvaluationModelMap R)
    (boundedAboveFlatAffineEvaluationModelMap S) (boundedAboveFlatAffinePullbackModelMap f)
    (boundedAboveFlatAffineSectionsMap f) (boundedAboveFlatAffineOriginalEvaluation S)
    (boundedAboveFlatAffineOriginalEvaluation R) (boundedAboveFlatAffineNormalizedPullback f)
    (boundedAboveFlatAffineEvaluationCoefficientIso f)
    (boundedAboveFlatAffineEvaluationModelIso_source f)
    (boundedAboveFlatAffineEvaluationModelIso_target f)
/-- The whole canonical comparison track for every coefficient map. -/
@[colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionSpectrumNaturality.lean:75-91"
    "adaptation" "Actual whole coefficient evaluation track with canonical chosen-zero \
      normalization"]
def boundedAboveFlatAffineEvaluationCoefficientHomotopy {R S : CommRingCat.{u}} (f : R ⟶ S) :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap S)
      (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f)) :=
  (prespectrumTransformationHomotopy
    (F := boundedAboveFlatAffineSectionModelMap f ≫ boundedAboveFlatAffineEvaluationModelMap S)
    (G := boundedAboveFlatAffineEvaluationModelMap R ≫ boundedAboveFlatAffinePullbackModelMap f)
    (boundedAboveFlatAffineEvaluationModelIso f).hom
    (fun x => (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).asSmall.weq_iso _ (by
      change IsIso ((boundedAboveFlatAffineEvaluationModelIso f).hom.app x)
      infer_instance))).cast (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _)
/-- The initial endpoint is the strict coefficient restriction followed by actual evaluation. -/
theorem boundedAboveFlatAffineEvaluationCoefficientHomotopy_at_zero
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level n (0, x) =
      (boundedAboveFlatAffineEvaluationPrespectrumMap S).map n
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map n x) :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).at_zero n x
/-- The final endpoint is actual evaluation followed by normalized geometric pullback. -/
theorem boundedAboveFlatAffineEvaluationCoefficientHomotopy_at_one
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level n (1, x) =
      (boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f)).map n
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map n x) :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).at_one n x
/-- The entire track fixes the original basepoint at every level. -/
theorem boundedAboveFlatAffineEvaluationCoefficientHomotopy_at_point
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level n
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)).point n :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).at_point n s
/-- Homotopy and structure coordinates are independent, including at level zero. -/
theorem boundedAboveFlatAffineEvaluationCoefficientHomotopy_comm
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level (n + 1)
        (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level n (s, x)) t :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy f).comm n s x t
/-- The actual coefficient K-map commutes with evaluation, without any flatness premise. -/
@[colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionSpectrumNaturality.lean:75-91"
    "ingredient" "K-map naturality deduced from the actual whole coefficient evaluation track"]
theorem boundedAboveFlatAffineEvaluationKEquiv_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (a : (boundedAboveFlatAffineSectionWaldhausen R).K n) :
    boundedAboveFlatAffineEvaluationKEquiv S n
        (KMap (boundedAboveFlatAffineSectionsMap_exact f) n a) =
      KMap (boundedAboveFlatPerfectPullback_isExact (Spec.map f)) n
        (boundedAboveFlatAffineEvaluationKEquiv R n a) := by
  apply (originalZeroSpaceEquiv
    (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace) n).injective
  rw [boundedAboveFlatAffineEvaluationKEquiv_zeroSpace,
    boundedAboveFlatAffineSectionZeroSpaceEquiv_naturality,
    exactOriginalZeroSpaceEquiv_naturality, boundedAboveFlatAffineEvaluationKEquiv_zeroSpace]
  have h := congrFun
    ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).homotopyGroupMap_eq 0 n)
    (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a)
  exact (HomotopyGroup.map_comp
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map 0)
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map_point 0)
    ((boundedAboveFlatAffineEvaluationPrespectrumMap S).map 0)
    ((boundedAboveFlatAffineEvaluationPrespectrumMap S).map_point 0)
    (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a)).symm.trans
      (h.trans (HomotopyGroup.map_comp
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map 0)
        ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map_point 0)
        ((boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f)).map 0)
        ((boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f)).map_point 0)
        (boundedAboveFlatAffineSectionZeroSpaceEquiv R n a)))
end AlgebraicGeometry.Scheme.Modules
