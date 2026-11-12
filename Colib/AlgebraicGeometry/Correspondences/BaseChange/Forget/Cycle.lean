/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.ForgetBaseProduct
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward

/-!
# Forgetting a separated base on native finite cycles

The map is finite pushforward along the closed immersion between the actual
products. Its image is in the native finite-correspondence subgroup because
the original projection to the source is unchanged. Every signed coefficient
is retained. No composition law or transfer functor is asserted here.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Cycle.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380` and its `Support.lean`
prerequisite, using native `AlgebraicCycle` instead of a second cycle model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) (f : X ⟶ T) (g : Y ⟶ T)
  [IsSeparated r] [LocallyOfFiniteType r] [IsSeparated g] [LocallyOfFiniteType g]

/-- The unchanged source projection makes the actual pushed cycle admissible. -/
theorem finiteCyclePushforward_forgetBase_mem (c : finiteCorrespondences f g) :
    finiteCyclePushforward (forgetBaseProductMap r f g) c.val ∈
      finiteCorrespondences (f ≫ r) (g ≫ r) := by
  apply finiteCyclePushforward_mem_finiteCorrespondences (f ≫ r) (g ≫ r)
    (forgetBaseProductMap r f g) c.val c.property.1
  · intro z hz
    simpa only [Category.assoc, forgetBaseProductMap_fst] using (c.property.2 z hz).1
  · intro z hz
    simpa only [Category.assoc, forgetBaseProductMap_fst] using (c.property.2 z hz).2

/-- Forget the base by actual finite pushforward of native signed cycles. -/
def finiteCorrespondencesForgetBase :
    finiteCorrespondences f g →+ finiteCorrespondences (f ≫ r) (g ≫ r) where
  toFun c := ⟨finiteCyclePushforward (forgetBaseProductMap r f g) c.val,
    finiteCyclePushforward_forgetBase_mem r f g c⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (finiteCyclePushforward (forgetBaseProductMap r f g))
  map_add' c d := by
    apply Subtype.ext
    exact map_add (finiteCyclePushforward (forgetBaseProductMap r f g)) c.val d.val

/-- The underlying cycle is the existing finite pushforward, with no replacement. -/
@[simp]
theorem finiteCorrespondencesForgetBase_val (c : finiteCorrespondences f g) :
    (finiteCorrespondencesForgetBase r f g c).val =
      finiteCyclePushforward (forgetBaseProductMap r f g) c.val := rfl

/-- A closed product immersion retains every original coefficient exactly. -/
theorem finiteCorrespondencesForgetBase_apply (c : finiteCorrespondences f g)
    (z : pullback (C := Scheme) f g) :
    (finiteCorrespondencesForgetBase r f g c).val (forgetBaseProductMap r f g z) =
      c.val z :=
  finiteCyclePushforward_apply_of_isClosedImmersion (forgetBaseProductMap r f g) c.val z

/-- In particular, changing the base cannot annihilate an original signed cycle. -/
theorem finiteCorrespondencesForgetBase_injective :
    Function.Injective (finiteCorrespondencesForgetBase r f g) := by
  intro c d h
  apply Subtype.ext
  exact finiteCyclePushforward_injective_of_isClosedImmersion
    (forgetBaseProductMap r f g) (congrArg Subtype.val h)

end Stacks.Chow
