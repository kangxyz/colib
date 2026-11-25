/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareRectangleNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareTrackCompatibility

/-!
# The original double-square track comparison

The whole three-route comparison identifies the two exact exported geometric tracks at every
level. Adapted from Quillen bounded-flat `SquareTrack.lean` and `SquareTrackOriginal.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Equality of full levels identifies the entire original geometric square track. -/
theorem boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_eq {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) :
    boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h =
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy p v).symm.trans
        ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q w).cast
          (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap h).symm rfl) := by
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext n
  exact boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_level p v q w h n

namespace BoundedFlatPerfectDoubleSquareTrack

open BoundedFlatPerfectDoubleSquareCommonSimplex (total_eq)
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Paste the two original exported coefficient squares, retaining explicit association. -/
def originalLeft :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap p)
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy c q q' b hq)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy b p p' a hp).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap q'))

/-- Compare via the original source chart, outer square, and target chart tracks. -/
def originalRight :=
  (sourceChart p q c).symm.trans
    ((boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy c (q ≫ p) (q' ≫ p') a
      (total_eq p q p' q' a b c hp hq).symm).trans (targetChart p' q' a))

/-- The initial route retains both complete original exported square homotopies. -/
theorem originalLeft_level (n : ℕ) :
    (originalLeft p q p' q' a b c hp hq).level n =
      ((boundedAboveFlatPerfectDoubleSquareTrackComparison
        p q p' q' a b c hp hq).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold originalLeft
  rw [boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_eq,
    boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_eq,
    Homotopy.precomp_trans, Homotopy.precomp_symm,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr <;> rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The final route retains the complete original outer square homotopy. -/
theorem originalRight_level (n : ℕ) :
    (originalRight p q p' q' a b c hp hq).level n =
      ((boundedAboveFlatPerfectDoubleSquareTrackComparison
        p q p' q' a b c hp hq).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold originalRight
  rw [boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_eq]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- Actual double-square composition for the existing exported original tracks. -/
def originalComparison :
    (originalLeft p q p' q' a b c hp hq).RelHomotopy
      (originalRight p q p' q' a b c hp hq) :=
  Homotopy.RelHomotopy.ofLevels
    (boundedAboveFlatPerfectDoubleSquareTrackComparison p q p' q' a b c hp hq)
    _ _ (by intro n; simpa using originalLeft_level p q p' q' a b c hp hq n)
    (by intro n; simpa using originalRight_level p q p' q' a b c hp hq n)

end BoundedFlatPerfectDoubleSquareTrack
end AlgebraicGeometry.Scheme.Modules
