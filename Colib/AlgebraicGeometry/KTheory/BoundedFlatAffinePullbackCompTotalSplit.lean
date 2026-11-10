/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineNormalizationSplit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineGeometricCompositionLevels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.KTheory.Waldhausen.Iterated.SmallModelNativeNormalizationCompositionHomotopy
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffinePullbackModelConstructor
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationIsoConstructors

/-!
# The actual affine total composition track and the geometric split

The total track is the realization of the actual lifted normalized composition
constraint. Its comparison with geometric composition followed by canonical
normalization uses the proved factorization of that same constraint. The geometric
split keeps the contravariant Spec composition source cast. All comparisons retain
whole levels and the independent comparison, homotopy and structure coordinates.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem normalization_ofLevels_level_toContinuousMap
    {X Y : Topology.LoopPrespectrum.{u}}
    {f g f' g' : X ⟶ Y} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n)
    (hK : ∀ n, K'.level n = K.level n) (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap =
      (J.level n).toContinuousMap := by
  rfl

/-- The actual lifted total track is relatively homotopic to the existing geometric
split, without replacing its normalized constraint or its endpoint transports. -/
@[no_expose]
def boundedAboveFlatAffinePullbackCompTotalSplit
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffinePullbackCompHomotopy f g).RelHomotopy
      ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
        (Spec.map g) (Spec.map f)).cast
          (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map_comp f g).symm)
          rfl) := by
  refine (nativeModelAsSmallNormalizationCompTrackComparison
      (W := boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
      (V := boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
      (U := boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
      (hH := boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
      (hF := boundedAboveFlatPerfectPullback_isExact (Spec.map f))
      (hG := boundedAboveFlatPerfectPullback_isExact (Spec.map g))
      (i := boundedAboveFlatAffineGeometricCompIso f g)
      (i' := boundedAboveFlatAffineNormalizedCompIso f g)
      (hcomp := boundedAboveFlatAffineNormalizedCompIso_split_hom f g)
      (A := boundedAboveFlatAffinePullbackModelMap f)
      (B := boundedAboveFlatAffinePullbackModelMap g)
      (K := boundedAboveFlatAffinePullbackModelMap (f ≫ g))
      (hA := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap f)
      (hB := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap g)
      (hK := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap (f ≫ g))
      (μ := boundedAboveFlatAffinePullbackModelCompIso f g)
      (hμ := boundedAboveFlatAffinePullbackModelCompIso_eq f g)
      (hweak := fun x =>
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace).asSmall.weq_iso _ (by
          change IsIso ((boundedAboveFlatAffinePullbackModelCompIso f g).hom.app x)
          infer_instance))
      (hf := boundedAboveFlatAffinePullbackModelMap_prespectrum (f ≫ g))
      (hg := (prespectrumFunctor.map_comp
        (boundedAboveFlatAffinePullbackModelMap f)
        (boundedAboveFlatAffinePullbackModelMap g)).trans
          (congrArg₂ (fun a b => a ≫ b)
            (boundedAboveFlatAffinePullbackModelMap_prespectrum f)
            (boundedAboveFlatAffinePullbackModelMap_prespectrum g)))
      (hSource := boundedAboveFlatAffinePullbackModelMap_toFunctor (f ≫ g))
      (hTarget := boundedAboveFlatAffinePullbackModelComp_toFunctor f g)).ofLevels _ _ ?_ ?_
  · intro n
    unfold boundedAboveFlatAffinePullbackCompHomotopy
    exact (Homotopy.cast_level _ _ _ n).trans (Homotopy.cast_level _ _ _ n).symm
  · intro n
    exact (boundedAboveFlatAffineGeometricCompHomotopy_level f g n).symm

/-- The complete two-time affine comparison is the canonical normalization triangle. -/
theorem boundedAboveFlatAffinePullbackCompTotalSplit_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    ((boundedAboveFlatAffinePullbackCompTotalSplit f g).level n).toContinuousMap =
      ((exactNormalizationCompTrackComparison
        (boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
        (boundedAboveFlatPerfectPullback_isExact (Spec.map f))
        (boundedAboveFlatPerfectPullback_isExact (Spec.map g))
        (boundedAboveFlatAffineGeometricCompIso f g)).level n).toContinuousMap := by
  exact (normalization_ofLevels_level_toContinuousMap
    (nativeModelAsSmallNormalizationCompTrackComparison
      (W := boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
      (V := boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
      (U := boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
      (hH := boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
      (hF := boundedAboveFlatPerfectPullback_isExact (Spec.map f))
      (hG := boundedAboveFlatPerfectPullback_isExact (Spec.map g))
      (i := boundedAboveFlatAffineGeometricCompIso f g)
      (i' := boundedAboveFlatAffineNormalizedCompIso f g)
      (hcomp := boundedAboveFlatAffineNormalizedCompIso_split_hom f g)
      (A := boundedAboveFlatAffinePullbackModelMap f)
      (B := boundedAboveFlatAffinePullbackModelMap g)
      (K := boundedAboveFlatAffinePullbackModelMap (f ≫ g))
      (hA := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap f)
      (hB := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap g)
      (hK := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap (f ≫ g))
      (μ := boundedAboveFlatAffinePullbackModelCompIso f g)
      (hμ := boundedAboveFlatAffinePullbackModelCompIso_eq f g)
      (hweak := fun x =>
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace).asSmall.weq_iso _ (by
          change IsIso ((boundedAboveFlatAffinePullbackModelCompIso f g).hom.app x)
          infer_instance))
      (hf := boundedAboveFlatAffinePullbackModelMap_prespectrum (f ≫ g))
      (hg := (prespectrumFunctor.map_comp
        (boundedAboveFlatAffinePullbackModelMap f)
        (boundedAboveFlatAffinePullbackModelMap g)).trans
          (congrArg₂ (fun a b => a ≫ b)
            (boundedAboveFlatAffinePullbackModelMap_prespectrum f)
            (boundedAboveFlatAffinePullbackModelMap_prespectrum g)))
      (hSource := boundedAboveFlatAffinePullbackModelMap_toFunctor (f ≫ g))
      (hTarget := boundedAboveFlatAffinePullbackModelComp_toFunctor f g)) _ _ _ _ n).trans
    (nativeModelAsSmallNormalizationCompTrackComparison_level
      (W := boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
      (V := boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
      (U := boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
      (hH := boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
      (hF := boundedAboveFlatPerfectPullback_isExact (Spec.map f))
      (hG := boundedAboveFlatPerfectPullback_isExact (Spec.map g))
      (i := boundedAboveFlatAffineGeometricCompIso f g)
      (i' := boundedAboveFlatAffineNormalizedCompIso f g)
      (hcomp := boundedAboveFlatAffineNormalizedCompIso_split_hom f g)
      (A := boundedAboveFlatAffinePullbackModelMap f)
      (B := boundedAboveFlatAffinePullbackModelMap g)
      (K := boundedAboveFlatAffinePullbackModelMap (f ≫ g))
      (hA := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap f)
      (hB := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap g)
      (hK := boundedAboveFlatAffinePullbackModelMap_eq_asSmallCategoryMap (f ≫ g))
      (μ := boundedAboveFlatAffinePullbackModelCompIso f g)
      (hμ := boundedAboveFlatAffinePullbackModelCompIso_eq f g)
      (hweak := fun x =>
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace).asSmall.weq_iso _ (by
          change IsIso ((boundedAboveFlatAffinePullbackModelCompIso f g).hom.app x)
          infer_instance))
      (hf := boundedAboveFlatAffinePullbackModelMap_prespectrum (f ≫ g))
      (hg := (prespectrumFunctor.map_comp
        (boundedAboveFlatAffinePullbackModelMap f)
        (boundedAboveFlatAffinePullbackModelMap g)).trans
          (congrArg₂ (fun a b => a ≫ b)
            (boundedAboveFlatAffinePullbackModelMap_prespectrum f)
            (boundedAboveFlatAffinePullbackModelMap_prespectrum g)))
      (hSource := boundedAboveFlatAffinePullbackModelMap_toFunctor (f ≫ g))
      (hTarget := boundedAboveFlatAffinePullbackModelComp_toFunctor f g) n)

end AlgebraicGeometry.Scheme.Modules
