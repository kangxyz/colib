/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffinePullbackCompTotalSplit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompTracks
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# The actual section total route and geometric split route

Precompose the actual pullback total/split comparison by evaluation and paste it
with the unchanged composite coefficient track. These routes use the same
right-associated endpoint as the existing direct and iterated routes. The original
left-associated endpoint is recovered by their common categorical association cast.
This module does not assert the separate total-to-iterated whole-level comparison.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluate the composite coefficient, then use the actual geometric split track
with its Spec composition source cast. -/
def boundedAboveFlatAffineEvaluationCompSplitHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy (boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap T)
      (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        (prespectrumMap (boundedAboveFlatAffinePullbackModelMap f) ≫
          prespectrumMap (boundedAboveFlatAffinePullbackModelMap g))) :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy (f ≫ g)).trans
    (Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
        (Spec.map g) (Spec.map f)).cast
          (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map_comp f g).symm)
          rfl))

/-- Paste the unchanged coefficient track with the precomposed normalization triangle. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationCompTotalSplit
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).RelHomotopy
      (boundedAboveFlatAffineEvaluationCompSplitHomotopy f g) :=
  (Homotopy.RelHomotopy.refl
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy (f ≫ g))).hcomp
      (Homotopy.RelHomotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (boundedAboveFlatAffinePullbackCompTotalSplit f g))

/-- Comparison time zero is the unchanged total coefficient route. -/
theorem boundedAboveFlatAffineEvaluationCompTotalSplit_at_zero
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (0, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).level n (s, x) :=
  ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n).apply_zero (s, x)

/-- Comparison time one is the whole geometric split coefficient route. -/
theorem boundedAboveFlatAffineEvaluationCompTotalSplit_at_one
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (1, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompSplitHomotopy f g).level n (s, x) :=
  ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n).apply_one (s, x)

/-- Both original endpoint maps stay fixed throughout the source boundary. -/
theorem boundedAboveFlatAffineEvaluationCompTotalSplit_source
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (r, (0, x)) =
      (boundedAboveFlatAffineEvaluationPrespectrumMap T).map n
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g)).map n x) :=
  (((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n).eq_fst r (Or.inl rfl)).trans
    ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).at_zero n x)

/-- The target boundary is the original evaluation followed by the two pullback maps. -/
theorem boundedAboveFlatAffineEvaluationCompTotalSplit_target
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (r, (1, x)) =
      (prespectrumMap (boundedAboveFlatAffinePullbackModelMap g)).map n
        ((prespectrumMap (boundedAboveFlatAffinePullbackModelMap f)).map n
          ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map n x)) :=
  (((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n).eq_fst r
    (Or.inr (Or.inl rfl))).trans
      ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).at_one n x)

/-- Every comparison slice fixes the entire original point line. -/
theorem boundedAboveFlatAffineEvaluationCompTotalSplit_point
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s : unitInterval) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).point n :=
  (((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n).eq_fst r
    (Or.inr (Or.inr rfl))).trans
      ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).at_point n s)

/-- Comparison, path and structure coordinates are independent, including level zero. -/
theorem boundedAboveFlatAffineEvaluationCompTotalSplit_comm
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompTotalSplit f g).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n (r, (s, x))) t :=
  (boundedAboveFlatAffineEvaluationCompTotalSplit f g).comm n r s x t

end AlgebraicGeometry.Scheme.Modules
