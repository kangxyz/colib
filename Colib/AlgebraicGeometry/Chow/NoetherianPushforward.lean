/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The native weighted cycle map from a Noetherian scheme

Every native cycle on a Noetherian scheme has finite support. Consequently the existing native
cycle map with constant dimension weights is additive and compositional even when the ambient
map is not finite. Its use for correspondences still requires finiteness on the actual supports;
no admissibility or proper-pushforward-on-Chow-groups claim follows from this construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {X Y Z : Scheme.{u}}

/-- The original native weighted map, with additivity supplied by finite cycle support. -/
def noetherianCyclePushforward [IsNoetherian X] (f : X ⟶ Y) :
    AlgebraicCycle X ℤ →+ AlgebraicCycle Y ℤ where
  toFun := AlgebraicCycle.map f (fun _ : X => (0 : ℕ)) (fun _ : Y => (0 : ℕ))
  map_zero' := by
    apply Function.locallyFinsuppWithin.ext
    intro y
    simp [AlgebraicCycle.map, Function.locallyFinsupp.map, AlgebraicCycle.mapCoeff]
  map_add' a b := by
    apply Function.locallyFinsuppWithin.ext
    intro y
    simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
      AlgebraicCycle.mapCoeff, ite_true, Function.locallyFinsuppWithin.coe_add,
      Pi.add_apply, add_mul]
    apply finsum_mem_add_distrib'
    · exact a.finite_support.subset (fun x hx hz => hx.2 (by simp only [hz, zero_mul]))
    · exact b.finite_support.subset (fun x hx hz => hx.2 (by simp only [hz, zero_mul]))

/-- This extension agrees literally with the existing finite pushforward. -/
theorem noetherianCyclePushforward_eq_finiteCyclePushforward [IsNoetherian X]
    (f : X ⟶ Y) [IsFinite f] : noetherianCyclePushforward f = finiteCyclePushforward f := rfl

/-- The full fibre sum retains every signed coefficient and every residue degree. -/
theorem noetherianCyclePushforward_apply [IsNoetherian X] (f : X ⟶ Y)
    (c : AlgebraicCycle X ℤ) (y : Y) :
    noetherianCyclePushforward f c y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, c x * (f.residueDegree x : ℤ) := by
  simp [noetherianCyclePushforward, AlgebraicCycle.map, AlgebraicCycle.mapCoeff]

/-- A single source point has its actual image and residue-field degree. -/
theorem noetherianCyclePushforward_single [IsNoetherian X] (f : X ⟶ Y)
    (x : X) (n : ℤ) :
    noetherianCyclePushforward f (single x n) =
      single (f x) (n * (f.residueDegree x : ℤ)) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [noetherianCyclePushforward_apply, ← finsum_set_coe_eq_finsum_mem]
  by_cases hy : y = f x
  · subst y
    rw [finsum_eq_single _ ⟨x, by simp⟩]
    · simp
    · intro z hz
      have hzx : (z : X) ≠ x := fun he => hz (Subtype.ext he)
      simp [single_apply, hzx]
  · have hxy : f x ≠ y := Ne.symm hy
    rw [finsum_eq_zero_of_forall_eq_zero]
    · simp [single_apply, hy]
    · intro z
      have hzx : (z : X) ≠ x := fun he => hxy (by simpa [he] using z.2)
      simp [single_apply, hzx]

/-- Composition is proved on the original finite source support, so image collisions do not
require an injectivity assumption. The residue degrees multiply in the actual field tower. -/
theorem noetherianCyclePushforward_comp_apply [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ Z) (c : AlgebraicCycle X ℤ) :
    noetherianCyclePushforward g (noetherianCyclePushforward f c) =
      noetherianCyclePushforward (f ≫ g) c := by
  classical
  rw [← sum_apply_smul_single_eq_self_on_univ c.finite_support]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [noetherianCyclePushforward_single, noetherianCyclePushforward_single,
    noetherianCyclePushforward_single, residueDegree_comp, Nat.cast_mul]
  simp only [Scheme.Hom.comp_apply]
  congr 1
  ring

end Stacks.Chow
