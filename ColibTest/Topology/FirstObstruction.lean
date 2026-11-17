/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FirstObstruction

/-! Degree-two/three, singleton, and disconnected-space first-obstruction tests. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Topology Convexity FundamentalGroupoid.LocalCoefficients
universe u

namespace ColibTest.FirstObstruction

variable {X : Type u} [TopologicalSpace X]

/-- The degree-two specialization keeps the actual fundamental-group
vanishing hypothesis and genuine integral second homology. -/
theorem degreeTwo [PathConnectedSpace X] (z : X)
    (hπ : ∀ x : X, Subsingleton (HomotopyGroup.Pi 1 X x))
    (hH : IsZero (homology (constant X integralCoefficients.{u}) 2)) :
    Subsingleton (HomotopyGroup.Pi 2 X z) := by
  apply subsingleton_pi_of_homology_isZero 0 z ?_ hH
  intro x k hk hlt
  have h : k = 1 := by omega
  subst k
  exact hπ x

/-- Degree three requires both lower positive original homotopy groups. -/
theorem degreeThree [PathConnectedSpace X] (z : X)
    (hπ₁ : ∀ x : X, Subsingleton (HomotopyGroup.Pi 1 X x))
    (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup.Pi 2 X x))
    (hH : IsZero (homology (constant X integralCoefficients.{u}) 3)) :
    Subsingleton (HomotopyGroup.Pi 3 X z) := by
  apply subsingleton_pi_of_homology_isZero 1 z ?_ hH
  intro x k hk hlt
  have h : k = 1 ∨ k = 2 := by omega
  rcases h with rfl | rfl
  · exact hπ₁ x
  · exact hπ₂ x

/-- On an actual singleton subspace, all hypotheses are supplied by the
proved positive point homology calculation and the original loop quotient. -/
theorem singleton_space (z : X) (m : ℕ) :
    Subsingleton (HomotopyGroup.Pi (m + 2) ({z} : Set X) ⟨z, rfl⟩) := by
  let : PathConnectedSpace ({z} : Set X) := {
    nonempty := ⟨⟨z, rfl⟩⟩
    joined := fun a b ↦ by
      have h : a = b := Subsingleton.elim _ _
      subst b
      exact Joined.refl a }
  apply subsingleton_pi_of_homology_isZero (X := ({z} : Set X)) m ⟨z, rfl⟩
  · intro x k _ _
    refine ⟨fun a b ↦ ?_⟩
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    exact congrArg Quotient.mk' (GenLoop.ext p q (fun _ ↦ Subsingleton.elim _ _))
  · exact point_constant_homology_isZero z integralCoefficients.{u} (m + 1)

/-- Positive integral homology can vanish in every degree while Pi zero has
more than one element: discrete Bool guards the retained connectivity input. -/
theorem disconnected_bool_guard :
    (∀ n : ℕ, IsZero (homology (constant Bool integralCoefficients.{0}) (n + 1))) ∧
      ¬ Subsingleton (HomotopyGroup.Pi 0 Bool false) := by
  constructor
  · intro n
    exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) (n + 1) integralCoefficients.{0} (TopCat.of Bool)
      (Nat.succ_ne_zero n)).of_iso (constantHomologyIso integralCoefficients.{0} (n + 1))
  · intro h
    let := h
    have hz : Subsingleton (ZerothHomotopy Bool) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false)).symm.injective.subsingleton
    let : PathConnectedSpace Bool :=
      pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk false⟩, hz⟩
    let : Subsingleton Bool := subsingleton_of_preconnected_totallyDisconnected
    have hfalse : (false : Bool) = true := Subsingleton.elim _ _
    cases hfalse

/-- The additive theorem's degree parameter cannot silently become degree one. -/
theorem degreeOne_excluded : ¬ ∃ m : ℕ, m + 2 = 1 := by omega

/-- Mathlib's singular-homology functor is accepted directly. -/
theorem originalSingularHomology_endpoint [PathConnectedSpace X] (m : ℕ) (z : X)
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ)
      (m + 2)).obj integralCoefficients.{u}).obj (TopCat.of X))) :
    Subsingleton (HomotopyGroup.Pi (m + 2) X z) :=
  subsingleton_pi_of_singularHomology_isZero m z hs hH

/-- The original spherical map is nullhomotopic relative to its whole boundary. -/
theorem fixedBoundary_endpoint [PathConnectedSpace X] (m : ℕ) (z : X)
    (f : SphericalSimplex X z (m + 2))
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (homology (constant X integralCoefficients.{u}) (m + 2))) :
    f.val.HomotopicRel (ContinuousMap.const _ z) (StdSimplex.boundary (m + 2)) :=
  spherical_nullhomotopic_of_homology_isZero m z f hs hH

#print axioms subsingleton_pi_of_singularHomology_isZero
#print axioms spherical_nullhomotopic_of_homology_isZero

end ColibTest.FirstObstruction
