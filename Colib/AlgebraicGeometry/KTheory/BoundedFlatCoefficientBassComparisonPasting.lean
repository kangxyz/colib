/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassChartPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Whole boundary levels of the actual coefficient Bass pasting

Identify both original boundary tracks at each level, then use those same whole tracks in the
native moving-pushout descent interface. No new endpoint homotopies are supplied.

Implementation provenance: Quillen `BoundedFlat/CoefficientBassMap.lean:226-268,288-298`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b)

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

/-- The initial boundary is the entire original Bass square under coefficient change. -/
theorem boundedAboveFlatCoefficientBassBoundary_source_level (n : ℕ) :
    ((boundedAboveFlatCoefficientBassSquareHomotopy P a).postcomp
      (K (coefficientMap P ((laurentUnderFunctor R).map g)))).level n =
      ((boundedAboveFlatCoefficientBassBoundary P g).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  simp only [boundedAboveFlatCoefficientBassSquareHomotopy, Homotopy.postcomp_trans,
    Homotopy.postcomp_symm]

/-- The constructed boundary ends at the original Bass target cylinder with exact associations. -/
theorem boundedAboveFlatCoefficientBassBoundary_target_level (n : ℕ) :
    (boundedAboveFlatCoefficientBassPastedTrack P g).level n =
      ((boundedAboveFlatCoefficientBassBoundary P g).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · unfold boundedAboveFlatCoefficientBassSquareHomotopy
          rw [Homotopy.precomp_trans, Homotopy.precomp_symm]
          apply Homotopy.trans_level_congr
          · apply Homotopy.symm_level_congr
            rfl
          · rfl
        · exact congrArg (fun H ↦ H.level n)
            (Homotopy.postcomp_symm (boundedAboveFlatCoefficientPolynomialSquareHomotopy P g)
              (K (laurentMinus P b)))
  · rfl

/-- The original Bass square satisfies the actual coefficient pasted-track relation. -/
def boundedAboveFlatCoefficientBassPasting :
    ((boundedAboveFlatCoefficientBassSquareHomotopy P a).postcomp
      (K (coefficientMap P ((laurentUnderFunctor R).map g)))).RelHomotopy
      (boundedAboveFlatCoefficientBassPastedTrack P g) :=
  Homotopy.RelHomotopy.ofLevels (boundedAboveFlatCoefficientBassBoundary P g) _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      boundedAboveFlatCoefficientBassBoundary_source_level P g n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      boundedAboveFlatCoefficientBassBoundary_target_level P g n)

/-- The genuine geometric boundary filler in the exact moving-pushout descent interface. -/
def boundedAboveFlatCoefficientBassDescPasting :
    (boundedAboveFlatCoefficientBassSourceDescTrack P g).RelHomotopy
      (boundedAboveFlatCoefficientBassPastedDescTrack P g) :=
  Homotopy.RelHomotopy.ofLevels (boundedAboveFlatCoefficientBassPasting P g) _ _ (fun _ ↦ rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · apply Homotopy.symm_level_congr
        rfl)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassMap.lean:226-298"
  "adaptation" "The actual boundary levels and the original moving-square endpoint tracks."]
  boundedAboveFlatCoefficientBassBoundary_source_level
  boundedAboveFlatCoefficientBassBoundary_target_level
  boundedAboveFlatCoefficientBassDescPasting

end AlgebraicGeometry.Scheme.Modules
