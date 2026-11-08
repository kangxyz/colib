/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Basic

/-!
# Additive extension on native finite correspondences

A family of values on the actual admissible points extends additively to native
finite correspondences by the signed finite sum of their coefficients. This
works directly on the native cycle subgroup; no equivalence to a second `Finsupp`
presentation is introduced. The finite-support condition makes every sum genuine.

This replaces the additive-extension use of `Finsupp.liftAddHom` in the source
`motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/TorCycle.lean`.
It supplies an additive construction, not a proof of any geometric composition law.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u v

namespace Stacks.Chow

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- A signed prime correspondence as an element of the actual native subgroup. -/
def singleFiniteCorrespondence (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) (n : ℤ) : finiteCorrespondences f g :=
  ⟨single z n, single_mem_finiteCorrespondences f g z hz n⟩

variable {A : Type v} [AddCommGroup A]
variable (φ : ∀ z : pullback (C := Scheme) f g, IsFiniteCorrespondencePoint f g z → A)

/-- The signed contribution of one actual point to an additive extension. -/
def finiteCorrespondenceContribution (c : finiteCorrespondences f g)
    (z : pullback (C := Scheme) f g) : A :=
  if hz : IsFiniteCorrespondencePoint f g z then c.val z • φ z hz else 0

/-- Only the finite support of the original correspondence can contribute. -/
theorem finite_support_finiteCorrespondenceContribution (c : finiteCorrespondences f g) :
    (Function.support (finiteCorrespondenceContribution f g φ c)).Finite := by
  apply c.property.1.subset
  intro z hz hc
  exact hz (by simp [finiteCorrespondenceContribution, hc])

/-- Extend values on actual admissible points by their integer coefficients. -/
def liftFiniteCorrespondence : finiteCorrespondences f g →+ A where
  toFun c := ∑ᶠ z, finiteCorrespondenceContribution f g φ c z
  map_zero' := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    simp [finiteCorrespondenceContribution]
  map_add' c d := by
    have heq : finiteCorrespondenceContribution f g φ (c + d) =
        finiteCorrespondenceContribution f g φ c +
          finiteCorrespondenceContribution f g φ d := by
      funext z
      by_cases hz : IsFiniteCorrespondencePoint f g z <;>
        simp [finiteCorrespondenceContribution, hz, add_zsmul]
    change (∑ᶠ z, finiteCorrespondenceContribution f g φ (c + d) z) = _
    rw [heq]
    exact finsum_add_distrib
      (finite_support_finiteCorrespondenceContribution f g φ c)
      (finite_support_finiteCorrespondenceContribution f g φ d)

/-- A signed prime is sent to its prescribed value with exactly the same integer weight. -/
@[simp]
theorem liftFiniteCorrespondence_single
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) (n : ℤ) :
    liftFiniteCorrespondence f g φ (singleFiniteCorrespondence f g z hz n) = n • φ z hz := by
  classical
  change (∑ᶠ x, finiteCorrespondenceContribution f g φ
    (singleFiniteCorrespondence f g z hz n) x) = _
  rw [finsum_eq_single _ z]
  · simp [finiteCorrespondenceContribution, singleFiniteCorrespondence, hz]
  · intro x hx
    simp [finiteCorrespondenceContribution, singleFiniteCorrespondence, single_apply, hx]

end Stacks.Chow
