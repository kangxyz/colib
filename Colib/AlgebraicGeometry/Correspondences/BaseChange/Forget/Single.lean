/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Cycle
public import Colib.AlgebraicGeometry.Correspondences.Additive

/-!
# Admissible primes after forgetting the base

The original coefficient-one cycle detects admissibility of its actual image.
Closed-immersion pushforward then preserves every signed coefficient.
Adapted from the prime-pushforward argument in
`Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Cycle.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`, on native cycle groups.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) (f : X ⟶ T) (g : Y ⟶ T)
  [IsSeparated r] [LocallyOfFiniteType r] [IsSeparated g] [LocallyOfFiniteType g]

/-- The image of an admissible prime is admissible over the smaller base. -/
theorem isFiniteCorrespondencePoint_forgetBase (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) :
    IsFiniteCorrespondencePoint (f ≫ r) (g ≫ r) (forgetBaseProductMap r f g z) := by
  classical
  let c := finiteCorrespondencesForgetBase r f g (singleFiniteCorrespondence f g z hz 1)
  apply c.property.2
  change (finiteCorrespondencesForgetBase r f g
    (singleFiniteCorrespondence f g z hz 1)).val (forgetBaseProductMap r f g z) ≠ 0
  rw [finiteCorrespondencesForgetBase_apply]
  simp [singleFiniteCorrespondence]

/-- The image prime has the original signed coefficient, without a degree factor. -/
@[simp]
theorem finiteCorrespondencesForgetBase_single (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) (n : ℤ) :
    finiteCorrespondencesForgetBase r f g (singleFiniteCorrespondence f g z hz n) =
      singleFiniteCorrespondence (f ≫ r) (g ≫ r) (forgetBaseProductMap r f g z)
        (isFiniteCorrespondencePoint_forgetBase r f g z hz) n := by
  apply Subtype.ext
  exact finiteCyclePushforward_single_of_isClosedImmersion (forgetBaseProductMap r f g) z n

end Stacks.Chow
