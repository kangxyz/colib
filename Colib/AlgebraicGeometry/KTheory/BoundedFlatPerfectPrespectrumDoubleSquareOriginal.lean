/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitSquare
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Vertical comparison for the exported geometric square tracks

The routes use the actual pullback square tracks, not just the endpoint maps. Their complete
levels identify the two boundaries of the split-triple comparison. In Colib the exported
square is already defined by the split track with explicit transport.

Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrackOriginal.lean:36-81`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules.DoubleSquareTrack

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "squareTrack" => boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Paste the two original exported coefficient squares, retaining explicit association. -/
def originalLeft :=
  ((Homotopy.precomp (K p)
    (squareTrack c q q' b hq)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((squareTrack b p p' a hp).postcomp
      (K q'))

/-- Compare via the original source chart, outer square, and target chart tracks. -/
def originalRight :=
  (sourceChart p q c).symm.trans
    ((squareTrack c (q ≫ p) (q' ≫ p') a
      (total_eq p q p' q' a b c hp hq).symm).trans (targetChart p' q' a))

/-- The initial route retains both complete original exported square homotopies. -/
theorem originalLeft_level (n : ℕ) :
    (originalLeft p q p' q' a b c hp hq).level n =
    ((boundedAboveFlatPerfectDoubleSquareTrackComparison p q p' q' a b c hp hq).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold originalLeft boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
  rw [Homotopy.precomp_trans, Homotopy.precomp_symm,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr <;> rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The final route retains the complete original outer square homotopy. -/
theorem originalRight_level (n : ℕ) :
    (originalRight p q p' q' a b c hp hq).level n =
    ((boundedAboveFlatPerfectDoubleSquareTrackComparison p q p' q' a b c hp hq).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold originalRight boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- Actual double-square composition for the existing exported original tracks. -/
def originalComparison :
    (originalLeft p q p' q' a b c hp hq).RelHomotopy
      (originalRight p q p' q' a b c hp hq) :=
  Homotopy.RelHomotopy.ofLevels
    (boundedAboveFlatPerfectDoubleSquareTrackComparison p q p' q' a b c hp hq) _ _
    (fun n ↦ by
      simpa only [Homotopy.RelHomotopy.at_zero] using originalLeft_level p q p' q' a b c hp hq n)
    (fun n ↦ by
      simpa only [Homotopy.RelHomotopy.at_one] using originalRight_level p q p' q' a b c hp hq n)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrackOriginal.lean:36-81"
  "adaptation" "Vertical comparison of both complete exported geometric square routes."]
  originalComparison

end AlgebraicGeometry.Scheme.Modules.DoubleSquareTrack
