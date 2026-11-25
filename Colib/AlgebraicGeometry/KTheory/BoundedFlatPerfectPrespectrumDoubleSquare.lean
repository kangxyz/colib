/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumAssociativity
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.RelativeHomotopyThreeRoutes

/-!
# Vertical pasting of the actual split bounded-flat pullback tracks

The two squares share an actual intermediate pullback route. Their commutativity equations
transport the complete level tracks, and the three original split-triple comparisons paste to
a relative homotopy of the two outer routes.

Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrack.lean:27-156`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "splitTrack" => boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy

namespace DoubleSquareTrack
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

include hq in
/-- The first commuting square identifies the two original triple composites. -/
theorem middle_eq : q' ≫ b ≫ p = c ≫ q ≫ p := by
  rw [← Category.assoc, ← hq, Category.assoc]

include hp hq in
/-- Both commuting squares identify the original outer triple composite. -/
theorem total_eq : (q' ≫ p') ≫ a = c ≫ q ≫ p := by
  rw [Category.assoc, ← hp]
  exact middle_eq p q q' b c hq

/-- The original sourceTotal track in the double-square diagram. -/
def sourceTotal :=
  splitTrack c (q ≫ p)

/-- The original sourceChart track in the double-square diagram. -/
def sourceChart :=
  (splitTrack q p).postcomp (K c)

/-- The original firstIntermediate track in the double-square diagram. -/
def firstIntermediate :=
  (splitTrack (c ≫ q) p).cast
  (congrArg K (Category.assoc c q p)) rfl

/-- The original firstRestriction track in the double-square diagram. -/
def firstRestriction :=
  (Homotopy.precomp (K p)
  (splitTrack c q)).cast rfl (Category.assoc _ _ _).symm

/-- The original middleTotal track in the double-square diagram. -/
def middleTotal :=
  (splitTrack q' (b ≫ p)).cast
  (congrArg K (middle_eq p q q' b c hq)) rfl

/-- The original middleChart track in the double-square diagram. -/
def middleChart :=
  (splitTrack b p).postcomp (K q')

/-- The original secondRestriction track in the double-square diagram. -/
def secondRestriction :=
  (Homotopy.precomp (K p)
  (splitTrack q' b)).cast
  (congrArg (fun k ↦ K p ≫ K k) hq.symm) (Category.assoc _ _ _).symm

/-- The original targetTotal track in the double-square diagram. -/
def targetTotal :=
  (splitTrack (q' ≫ p') a).cast
  (congrArg K (total_eq p q p' q' a b c hp hq)) rfl

/-- The original targetChart track in the double-square diagram. -/
def targetChart :=
  (Homotopy.precomp (K a)
  (splitTrack q' p')).cast rfl (Category.assoc _ _ _).symm

/-- The original lastRestriction track in the double-square diagram. -/
def lastRestriction :=
  ((splitTrack p' a).postcomp
  (K q')).cast
  (congrArg (fun k ↦ K k ≫ K q') hp.symm) rfl

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
  · change (splitTrack (c ≫ q) p).level n =
      (splitTrack (q' ≫ b) p).level n
    exact congrArg (fun k ↦ (splitTrack k p).level n) hq
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
  · change (splitTrack q' (b ≫ p)).level n =
      (splitTrack q' (p' ≫ a)).level n
    exact congrArg (fun k ↦ (splitTrack q' k).level n) hp
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

end DoubleSquareTrack

/-- Three genuine geometric triple comparisons supply the actual double-square pasting filler. -/
def boundedAboveFlatPerfectDoubleSquareTrackComparison
    {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b) :=
  Homotopy.RelHomotopy.threeRoutes
    (DoubleSquareTrack.firstTriple (p := p) (q := q) (c := c))
    (DoubleSquareTrack.middleTriple (p := p) (q := q) (q' := q') (b := b) (c := c) (hq := hq))
    (DoubleSquareTrack.lastTriple (p := p) (q := q) (p' := p') (q' := q')
      (a := a) (b := b) (c := c) (hp := hp) (hq := hq))

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrack.lean:27-156"
  "adaptation" "Vertical comparison retaining both exact outer tracks and their level transports."]
  boundedAboveFlatPerfectDoubleSquareTrackComparison

end AlgebraicGeometry.Scheme.Modules
