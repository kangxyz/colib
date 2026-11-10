/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompAssociation

/-! Actual total/split comparison equations with independent level and time variables. -/
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open scoped Topology unitInterval
universe u
noncomputable section

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    ((boundedAboveFlatAffinePullbackCompTotalSplit f g).level n).toContinuousMap =
      ((exactNormalizationCompTrackComparison
        (boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
        (boundedAboveFlatPerfectPullback_isExact (Spec.map f))
        (boundedAboveFlatPerfectPullback_isExact (Spec.map g))
        (boundedAboveFlatAffineGeometricCompIso f g)).level n).toContinuousMap :=
  boundedAboveFlatAffinePullbackCompTotalSplit_level f g n

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    ((boundedAboveFlatAffineEvaluationCompTotalSplitLeft f g).level n).toContinuousMap =
      ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n).toContinuousMap :=
  boundedAboveFlatAffineEvaluationCompTotalSplitLeft_level f g n

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level (0 + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap 0 x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).structureMap 0
        ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level 0 (r, (s, x))) t :=
  boundedAboveFlatAffineEvaluationCompTotalSplit_comm f g 0 r s t x
