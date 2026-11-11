/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompRelative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompAssociation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationPerfect
public import Colib.Topology.Prespectrum.RelativeHomotopySourceTransport

/-!
# The original geometric split route compares relatively with the whiskered route

The comparison is the inverse of the actual total-to-geometric-split comparison
followed by the actual total-to-whiskered comparison. The common association cast
retains the original left-associated target. No equality of parametrized paths is
asserted. All degrees and comparison, track and structure times remain independent.
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

/-- The unchanged whiskered route with the original left-associated target. -/
def boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy (a (f ≫ g) ≫ ε T)
      ((ε R ≫ prespectrumMap (P f)) ≫ prespectrumMap (P g)) :=
  (boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g).cast rfl
    (Category.assoc _ _ _).symm

/-- The common association transport preserves the entire whiskered level. -/
theorem boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy f g).level n =
      (boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g).level n :=
  Homotopy.cast_level _ _ _ n

/-- The original geometric split and whiskered routes compare relative to their endpoints. -/
@[no_expose, colib_tag "COL-0511",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      SectionCoefficientComposition.lean:107-113"
    "adaptation" "Original geometric split-to-whiskered relative comparison, retaining \
      whole levels and the common left-associated endpoint transport"]
def boundedAboveFlatAffineEvaluationCompSplitRelHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).RelHomotopy
      (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy f g) :=
  ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).symm.trans
    (boundedAboveFlatAffineEvaluationCompRelHomotopy f g)).ofLevels _ _
      (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy_level f g)
      (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy_level f g)

/-- Comparison time zero is the complete original geometric split route. -/
theorem boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_at_zero
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (0, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).level n (s, x) :=
  ((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n).apply_zero (s, x)

/-- Comparison time one is the complete iterated composition route. -/
theorem boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_at_one
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (1, (s, x)) =
      (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy f g).level n (s, x) :=
  ((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n).apply_one (s, x)

/-- The original source endpoint is fixed throughout the relative composition comparison. -/
theorem boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_source
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (r, (0, x)) =
      (ε T).map n ((a (f ≫ g)).map n x) :=
  (((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n).eq_fst r (Or.inl rfl)).trans
    ((boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).at_zero n x)

/-- The original target endpoint is fixed throughout the relative composition comparison. -/
theorem boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_target
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (r, (1, x)) =
      (prespectrumMap (P g)).map n ((prespectrumMap (P f)).map n ((ε R).map n x)) :=
  (((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n).eq_fst r
    (Or.inr (Or.inl rfl))).trans
      ((boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).at_one n x)

/-- Both homotopy coordinates fix the entire original point line. -/
theorem boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_point
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s : unitInterval) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n)) =
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).point n :=
  (((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n).eq_fst r
    (Or.inr (Or.inr rfl))).trans
      ((boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).at_point n s)

/-- Comparison, original track, and structure time are independent at every level. -/
theorem boundedAboveFlatAffineEvaluationCompSplitRelHomotopy_comm
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).level n (r, (s, x))) t :=
  (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).comm n r s x t

/-- Actual perfect inclusion postcomposes the entire split-to-whiskered comparison. -/
def boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    ((boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).postcomp
      (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec T).toRingedSpace)).RelHomotopy
      ((boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy f g).postcomp
        (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec T).toRingedSpace)) :=
  (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy f g).postcomp
    (boundedAboveFlatPerfectToPerfectPrespectrumMap (Spec T).toRingedSpace)

/-- Perfect postcomposition retains the independent prespectrum structure coordinate. -/
theorem boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy_comm
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (r s t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy f g).level (n + 1)
        (r, (s, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum (perfectComplexesWaldhausen (Spec T).toRingedSpace)).structureMap n
        ((boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy f g).level n
          (r, (s, x))) t :=
  (boundedAboveFlatAffineEvaluationCompSplitPerfectRelHomotopy f g).comm n r s x t

end AlgebraicGeometry.Scheme.Modules
