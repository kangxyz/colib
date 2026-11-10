/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompPasting
public import Colib.Topology.Prespectrum.RelativeHomotopySourceTransport

/-!
# Relative comparison of total and whiskered affine coefficient composition

The native pasting is transported by the two whole-level identifications. In particular,
this compares the total normalized track with the whiskered track as entire continuous
tracks. The geometric split track requires a separate normalization comparison.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
local notation "P" => boundedAboveFlatAffinePullbackModelMap
local notation "a" => boundedAboveFlatAffineSectionPrespectrumFunctor.map
local notation "ε" => boundedAboveFlatAffineEvaluationPrespectrumMap

private theorem affineRelativeOriginalPrespectrum_obj
    {C : Type*} [Category C] (W : Structure C) :
    originalPrespectrum W = prespectrum (asSmallCategory W) := by
  rfl

/-- The relative comparison of the total normalized and whiskered coefficient routes. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationCompRelHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).RelHomotopy
      (boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g) :=
  Homotopy.RelHomotopy.ofObjectLevels
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (affineRelativeOriginalPrespectrum_obj
      (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (boundedAboveFlatAffineEvaluationCompModelRelHomotopy f g)
    (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g)
    (boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g)
    (boundedAboveFlatAffineEvaluationCompDirectHomotopy_level_heq f g)
    (boundedAboveFlatAffineEvaluationCompIteratedHomotopy_level_heq f g)

/-- Comparison time zero is the complete direct composition route. -/
theorem boundedAboveFlatAffineEvaluationCompRelHomotopy_at_zero
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n (0, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).level n (s, x) :=
  ((boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n).apply_zero (s, x)

/-- Comparison time one is the complete iterated composition route. -/
theorem boundedAboveFlatAffineEvaluationCompRelHomotopy_at_one
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n (1, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g).level n (s, x) :=
  ((boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n).apply_one (s, x)

/-- The original source endpoint is fixed throughout the relative composition comparison. -/
theorem boundedAboveFlatAffineEvaluationCompRelHomotopy_source
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n (r, (0, x)) =
      (ε T).map n ((a (f ≫ g)).map n x) :=
  (((boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n).eq_fst r (Or.inl rfl)).trans
    ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).at_zero n x)

/-- The original target endpoint is fixed throughout the relative composition comparison. -/
theorem boundedAboveFlatAffineEvaluationCompRelHomotopy_target
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n (r, (1, x)) =
      (prespectrumMap (P g)).map n ((prespectrumMap (P f)).map n ((ε R).map n x)) :=
  (((boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n).eq_fst r
    (Or.inr (Or.inl rfl))).trans
      ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).at_one n x)

/-- Both homotopy coordinates fix the entire original point line. -/
theorem boundedAboveFlatAffineEvaluationCompRelHomotopy_point
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s : unitInterval) :
    (boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).point n :=
  (((boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n).eq_fst r
    (Or.inr (Or.inr rfl))).trans
      ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).at_point n s)

/-- Comparison, original track, and structure time are independent at every level. -/
theorem boundedAboveFlatAffineEvaluationCompRelHomotopy_comm
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCompRelHomotopy f g).level n (r, (s, x))) t :=
  (boundedAboveFlatAffineEvaluationCompRelHomotopy f g).comm n r s x t

end AlgebraicGeometry.Scheme.Modules
