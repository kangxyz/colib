/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareCommonSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumTripleTracks
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# The literal pullback tracks of two adjoining squares

The three native triple comparisons keep the common route terms and the actual endpoint
transports supplied by the commuting squares. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrack.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareTrack

open BoundedFlatPerfectDoubleSquareCommonSimplex (middle_eq total_eq)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The original sourceTotal track in the double-square diagram. -/
def sourceTotal :=
  boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy c (q ≫ p)

/-- The original sourceChart track in the double-square diagram. -/
def sourceChart :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q p).postcomp
  (boundedAboveFlatPerfectPullbackPrespectrumMap c)

/-- The original firstIntermediate track in the double-square diagram. -/
def firstIntermediate :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (c ≫ q) p).cast
  (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.assoc c q p)) rfl

/-- The original firstRestriction track in the double-square diagram. -/
def firstRestriction :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap p)
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy c q)).cast rfl (Category.assoc _ _ _).symm

/-- The original middleTotal track in the double-square diagram. -/
def middleTotal :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q' (b ≫ p)).cast
  (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (middle_eq p q q' b c hq)) rfl

/-- The original middleChart track in the double-square diagram. -/
def middleChart :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy b p).postcomp
  (boundedAboveFlatPerfectPullbackPrespectrumMap q')

/-- The original secondRestriction track in the double-square diagram. -/
def secondRestriction :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap p)
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q' b)).cast
  (congrArg (fun k ↦ boundedAboveFlatPerfectPullbackPrespectrumMap p ≫
    boundedAboveFlatPerfectPullbackPrespectrumMap k) hq.symm) (Category.assoc _ _ _).symm

/-- The original targetTotal track in the double-square diagram. -/
def targetTotal :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (q' ≫ p') a).cast
  (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (total_eq p q p' q' a b c hp hq)) rfl

/-- The original targetChart track in the double-square diagram. -/
def targetChart :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap a)
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q' p')).cast rfl
    (Category.assoc _ _ _).symm

/-- The original lastRestriction track in the double-square diagram. -/
def lastRestriction :=
  ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy p' a).postcomp
  (boundedAboveFlatPerfectPullbackPrespectrumMap q')).cast
  (congrArg (fun k ↦ boundedAboveFlatPerfectPullbackPrespectrumMap k ≫
    boundedAboveFlatPerfectPullbackPrespectrumMap q') hp.symm) rfl

/-- The first actual triple comparison, with the shared original route components. -/
def firstTriple : ((sourceTotal (p := p) (q := q) (c := c)).trans
      (sourceChart (p := p) (q := q) (c := c))).RelHomotopy
     ((firstIntermediate (p := p) (q := q) (c := c)).trans
      (firstRestriction (p := p) (q := q) (c := c))) :=
  Homotopy.RelHomotopy.ofLevels (boundedAboveFlatPerfectTripleTrackComparison c q p) _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The middle comparison source retains its entire original level. -/
theorem middle_left_level (n : ℕ) :
    ((middleTotal p q q' b c hq).trans (middleChart p q' b)).level n =
      (boundedAboveFlatPerfectTripleLeftTrack q' b p).level n := by
  apply Homotopy.trans_level_congr <;> rfl

/-- The middle comparison target uses only the actual commuting-square equation. -/
theorem middle_right_level (n : ℕ) :
    ((firstIntermediate p q c).trans (secondRestriction p q q' b c hq)).level n =
      (boundedAboveFlatPerfectTripleRightTrack q' b p).level n := by
  apply Homotopy.trans_level_congr
  · change (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (c ≫ q) p).level n =
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (q' ≫ b) p).level n
    exact congrArg (fun k ↦ (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy k p).level n)
      hq
  · rfl

/-- The middle actual triple comparison uses the genuine first commuting-square equation. -/
def middleTriple : ((middleTotal p q q' b c hq).trans (middleChart p q' b)).RelHomotopy
    ((firstIntermediate p q c).trans (secondRestriction p q q' b c hq)) :=
  Homotopy.RelHomotopy.ofLevels (boundedAboveFlatPerfectTripleTrackComparison q' b p) _ _
    (middle_left_level p q q' b c hq) (middle_right_level p q q' b c hq)

/-- The last comparison source uses only the actual second commuting-square equation. -/
theorem last_left_level (n : ℕ) :
    ((middleTotal p q q' b c hq).trans (lastRestriction p p' q' a b hp)).level n =
      (boundedAboveFlatPerfectTripleLeftTrack q' p' a).level n := by
  apply Homotopy.trans_level_congr
  · change (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q' (b ≫ p)).level n =
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q' (p' ≫ a)).level n
    exact congrArg (fun k ↦ (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q' k).level n)
      hp
  · rfl

/-- The last comparison target retains its entire original level. -/
theorem last_right_level (n : ℕ) :
    ((targetTotal p q p' q' a b c hp hq).trans (targetChart p' q' a)).level n =
      (boundedAboveFlatPerfectTripleRightTrack q' p' a).level n := by
  apply Homotopy.trans_level_congr <;> rfl

/-- The last actual triple comparison uses the genuine second commuting-square equation. -/
def lastTriple :
    ((middleTotal p q q' b c hq).trans (lastRestriction p p' q' a b hp)).RelHomotopy
      ((targetTotal p q p' q' a b c hp hq).trans (targetChart p' q' a)) :=
  Homotopy.RelHomotopy.ofLevels (boundedAboveFlatPerfectTripleTrackComparison q' p' a) _ _
    (last_left_level p q p' q' a b c hp hq) (last_right_level p q p' q' a b c hp hq)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareTrack
