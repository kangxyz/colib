/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareOriginal

/-!
# The actual common-projection route of a bounded-flat pullback double square

Identify the outer geometric square with the square of the two specified projections.
The original two chart tracks and all levels of the comparison are preserved.

Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrackProjection.lean:22-87`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules.DoubleSquareTrack

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "splitTrack" => boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
local notation "squareTrack" => boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (r' : C' ⟶ A') (hr : q ≫ p = r) (hr' : q' ≫ p' = r')

include hp hq hr hr' in
/-- The actual two chart squares induce the square between their common projections. -/
theorem outer_eq : c ≫ r = r' ≫ a := by
  rw [← hr, ← hr']
  exact (total_eq p q p' q' a b c hp hq).symm

/-- The original source chart composition, transported to the common projection. -/
def sourceProjection :=
  (splitTrack q p).cast
    (congrArg K hr) rfl

/-- The original target chart composition, transported to the common projection. -/
def targetProjection :=
  (splitTrack q' p').cast
    (congrArg K hr') rfl

/-- The entire actual outer square of common projections. -/
def outerProjectionSquare :=
  squareTrack c r r' a
    (outer_eq p q p' q' a b c hp hq r r' hr hr')

/-- The outer route retains both original chart composition tracks and the common square. -/
def reducedRight :=
  ((sourceProjection p q r hr).postcomp (K c)).symm.trans
    ((outerProjectionSquare p q p' q' a b c hp hq r r' hr hr').trans
      ((Homotopy.precomp (K a)
        (targetProjection p' q' r' hr')).cast rfl (Category.assoc _ _ _).symm))

/-- Projection identification preserves every point of the actual outer square track. -/
theorem outerProjectionSquare_level (n : ℕ) :
    (outerProjectionSquare p q p' q' a b c hp hq r r' hr hr').level n =
      (squareTrack c (q ≫ p) (q' ≫ p') a
        (total_eq p q p' q' a b c hp hq).symm).level n := by
  unfold outerProjectionSquare boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (splitTrack c r).level n (unitInterval.symm s, x) =
      (splitTrack c (q ≫ p)).level n (unitInterval.symm s, x)
    exact DFunLike.congr_fun
      (congrArg (fun k ↦ (splitTrack c k).level n) hr.symm) _
  · change (splitTrack r' a).level n =
      (splitTrack (q' ≫ p') a).level n
    exact congrArg (fun k ↦ (splitTrack k a).level n) hr'.symm

/-- The reduced outer route preserves the full previously constructed comparison boundary. -/
theorem reducedRight_level (n : ℕ) :
    (reducedRight p q p' q' a b c hp hq r r' hr hr').level n =
      (originalRight p q p' q' a b c hp hq).level n := by
  apply Homotopy.trans_level_congr
  · apply Homotopy.symm_level_congr
    apply Homotopy.postcomp_level_congr
    rfl
  · apply Homotopy.trans_level_congr
    · exact outerProjectionSquare_level p q p' q' a b c hp hq r r' hr hr' n
    · apply Homotopy.precomp_level_congr
      rfl

/-- Genuine double-square pasting through a specified common projection, using only geometry. -/
def projectionComparison :
    (originalLeft p q p' q' a b c hp hq).RelHomotopy
      (reducedRight p q p' q' a b c hp hq r r' hr hr') :=
  Homotopy.RelHomotopy.ofLevels (originalComparison p q p' q' a b c hp hq) _ _
    (fun _ ↦ rfl) (reducedRight_level p q p' q' a b c hp hq r r' hr hr')

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrackProjection.lean:22-87"
  "adaptation" "Same two chart tracks and common-projection route at every prespectrum level."]
  projectionComparison

end AlgebraicGeometry.Scheme.Modules.DoubleSquareTrack
