/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineNormalizationSplit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy
public import Colib.KTheory.Waldhausen.Iterated.IsoHomotopyCongruence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineGeometricIsoConstructor

/-!
# Whole-level affine geometric composition with its Spec transport

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

/-- The affine geometric iso and normalization give the existing geometric split,
including its actual contravariant Spec source transport, on every complete level. -/
theorem boundedAboveFlatAffineGeometricCompHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    ((exactOriginalPrespectrumIsoHomotopy
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
      (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
      (boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
      ((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).comp
        (boundedAboveFlatPerfectPullback_isExact (Spec.map g)))
      (boundedAboveFlatAffineGeometricCompIso f g)).trans
        (exactOriginalPrespectrumMapCompHomotopy
          (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
          (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace)
          (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
          (boundedAboveFlatPerfectPullback_isExact (Spec.map f))
          (boundedAboveFlatPerfectPullback_isExact (Spec.map g)))).level n =
      ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
        (Spec.map g) (Spec.map f)).cast
          (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map_comp f g).symm)
          rfl).level n := by
  refine Eq.trans ?_ (Homotopy.cast_level
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (Spec.map g) (Spec.map f))
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map_comp f g).symm)
    rfl n).symm
  unfold boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
  apply Homotopy.trans_level_congr
  · refine Eq.trans
      (exactOriginalPrespectrumIsoHomotopy_congr_level
        (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
        (boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
        ((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).comp
          (boundedAboveFlatPerfectPullback_isExact (Spec.map g)))
        (boundedAboveFlatAffineGeometricCompIso f g)
        (eqToIso (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≪≫
          boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f))
        (boundedAboveFlatAffineGeometricCompIso_eq_trans f g) n) ?_
    exact exactOriginalPrespectrumIsoHomotopy_eqToIso_trans_level
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
      (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)
      (boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
      (boundedAboveFlatPerfectPullback_isExact (Spec.map g ≫ Spec.map f))
      ((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).comp
        (boundedAboveFlatPerfectPullback_isExact (Spec.map g)))
      (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g))
      (boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)) n
  · rfl

end AlgebraicGeometry.Scheme.Modules
