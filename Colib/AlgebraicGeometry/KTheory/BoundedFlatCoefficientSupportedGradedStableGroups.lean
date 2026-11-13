/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedKGroups
public import Colib.KTheory.Waldhausen.Iterated.ModelStableKMap

/-! # Actual supported graded groups

Actual supported graded Model stable groups vanish in every signed degree other than zero.
The positive K dictionary and original Model connectivity are reused. No cone stability is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original positive graded K-groups identify with the same Model's positive stable groups. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:44"
  "adaptation" "Actual supported graded K-value and signed stable groups"]
theorem boundedAboveFlatCoefficientSupportedGradedOpen_stable_succ_subsingleton (a : Under R) (n :
  ℕ) :
    Subsingleton (stableHomotopyGroup (prespectrum
      (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a))
      ((n + 1 : ℕ) : ℤ)) := by
  let : Subsingleton
      ((boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K (n + 1)) :=
    boundedAboveFlatCoefficientSupportedGradedOpen_K_succ_subsingleton f T a n
  let e : Additive
      ((boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K (n + 1)) ≃+
      stableHomotopyGroup (prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a))
        ((n + 1 : ℕ) : ℤ) :=
    levelOneStableEquiv (prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a))
      (prespectrum_isOmega (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a)) (n + 1)
  exact e.symm.injective.subsingleton

/-- Actual Model connectivity gives negative signed stable vanishing without compactness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:60"
  "adaptation" "Actual supported graded K-value and signed stable groups"]
theorem boundedAboveFlatCoefficientSupportedGradedOpen_stable_neg_subsingleton
    (a : Under R) (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a)) d) :=
  prespectrum_stableHomotopyGroup_neg_subsingleton
    (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a) d hd

/-- The actual pointwise graded Model has no signed stable classes outside degree zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:68"
  "adaptation" "Actual supported graded K-value and signed stable groups"]
theorem boundedAboveFlatCoefficientSupportedGradedOpen_stable_subsingleton
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a)) d) := by
  by_cases hn : d < 0
  · exact boundedAboveFlatCoefficientSupportedGradedOpen_stable_neg_subsingleton f T a d hn
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    rw [he, hp]
    exact boundedAboveFlatCoefficientSupportedGradedOpen_stable_succ_subsingleton f T a (d.toNat -
      1)

end AlgebraicGeometry.Scheme.Modules
