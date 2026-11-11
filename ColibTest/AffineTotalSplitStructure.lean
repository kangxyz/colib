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
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (r, (1, x)) =
      (prespectrumMap (boundedAboveFlatAffinePullbackModelMap g)).map n
        ((prespectrumMap (boundedAboveFlatAffinePullbackModelMap f)).map n
          ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map n x)) :=
  boundedAboveFlatAffineEvaluationCompTotalSplit_target f g n r x

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s : unitInterval) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).point n :=
  boundedAboveFlatAffineEvaluationCompTotalSplit_point f g n r s

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (r, (s, x))) t :=
  boundedAboveFlatAffineEvaluationCompTotalSplit_comm f g n r s t x
