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
open AlgebraicGeometry.Scheme.Modules
open scoped Topology unitInterval
universe u
noncomputable section

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (0, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).level n (s, x) :=
  boundedAboveFlatAffineEvaluationCompTotalSplit_at_zero f g n s x

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (1, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompSplitHomotopy f g).level n (s, x) :=
  boundedAboveFlatAffineEvaluationCompTotalSplit_at_one f g n s x

example
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (r, (0, x)) =
      (boundedAboveFlatAffineEvaluationPrespectrumMap T).map n
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g)).map n x) :=
  boundedAboveFlatAffineEvaluationCompTotalSplit_source f g n r x
