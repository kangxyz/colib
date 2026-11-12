/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.GraphNaturality
public import Colib.RingTheory.Polynomial.ZeroNeighborhood.PencilBasic
import Mathlib.Algebra.Polynomial.Monic

/-!
# The quadratic family of two unit graphs

The monic pencil joins the split polynomial with roots `ab` and `1`
to the split polynomial with roots `a` and `b`. Both endpoints are
computed by graph restriction of the actual whole polynomial cycle.
This is the polynomial family used in the interchange argument in
Voevodsky, Cancellation theorem (2010), Lemma 4.8, following
Suslin and Voevodsky, Bloch-Kato conjecture and motivic cohomology
with finite coefficients, §3.4.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Polynomial TopologicalSpace Stacks.Chow
open Polynomial.ZeroNeighborhoodInterpolation

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {R : Type u} [CommRing R]

private def splitUnitPolynomial (a b : Rˣ) : R[X] :=
  (Polynomial.X - C (a : R)) * (Polynomial.X - C (b : R))

private theorem splitUnitPolynomial_monic (a b : Rˣ) : (splitUnitPolynomial a b).Monic :=
  (monic_X_sub_C _).mul (monic_X_sub_C _)

private theorem splitUnitPolynomial_natDegree [Nontrivial R] (a b : Rˣ) :
    (splitUnitPolynomial a b).natDegree = 2 := by
  unfold splitUnitPolynomial
  rw [(monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
  simp

private theorem splitUnitPolynomial_coeff_zero (a b : Rˣ) :
    (splitUnitPolynomial a b).coeff 0 = (a : R) * (b : R) := by
  simp [splitUnitPolynomial]

/-- The inner variable is the homotopy parameter and the outer variable is the
coordinate of the actual finite flat quadratic quotient. -/
def unitProductPencil (a b : Rˣ) : R[X][X] :=
  pencil ((Polynomial.X - C (↑(a * b) : R)) * (Polynomial.X - C (1 : R)))
    ((Polynomial.X - C (a : R)) * (Polynomial.X - C (b : R)))

theorem unitProductPencil_monic [Nontrivial R] (a b : Rˣ) :
    (unitProductPencil a b).Monic := by
  change (pencil (splitUnitPolynomial (a * b) 1) (splitUnitPolynomial a b)).Monic
  exact (pencil_monic_natDegree (splitUnitPolynomial_monic _ _) (splitUnitPolynomial_monic a b)
    ((splitUnitPolynomial_natDegree a b).trans (splitUnitPolynomial_natDegree _ _).symm)).1

theorem unitProductPencil_coeff_zero (a b : Rˣ) :
    (unitProductPencil a b).coeff 0 = C ((a : R) * (b : R)) := by
  change (pencil (splitUnitPolynomial (a * b) 1) (splitUnitPolynomial a b)).coeff 0 = _
  simp only [pencil_coeff, splitUnitPolynomial_coeff_zero,
    Units.val_mul, Units.val_one, mul_one]
  rw [← add_mul, sub_add_cancel, one_mul]

theorem unitProductPencil_constant_isUnit (a b : Rˣ) :
    IsUnit ((unitProductPencil a b).coeff 0) := by
  rw [unitProductPencil_coeff_zero]
  exact (a.isUnit.mul b.isUnit).map C

theorem unitProductPencil_map_eval_zero (a b : Rˣ) :
    (unitProductPencil a b).map (evalRingHom (0 : R)) =
      (Polynomial.X - C (↑(a * b) : R)) * (Polynomial.X - C (1 : R)) := by
  simp [unitProductPencil, pencil]

theorem unitProductPencil_map_eval_one (a b : Rˣ) :
    (unitProductPencil a b).map (evalRingHom (1 : R)) =
      (Polynomial.X - C (a : R)) * (Polynomial.X - C (b : R)) := by
  simp [unitProductPencil, pencil]

variable [IsNoetherianRing R]

private theorem polynomialCycle_eq_two_unitGraphs {S : Scheme.{u}} [_root_.IsReduced R]
    (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (u v : Rˣ) (h : p = (Polynomial.X - C (u : R)) * (Polynomial.X - C (v : R)))
    (hR : (genericPoints (Spec (.of R))).Finite) :
    polynomialCycle f p hp h0 = unitGraphCycle f u hR + unitGraphCycle f v hR := by
  subst p
  rw [polynomialCycle_mul f _ _ (monic_X_sub_C _) (monic_X_sub_C _)
    (linear_constant_isUnit u) (linear_constant_isUnit v), polynomialCycle_linear_graph,
    polynomialCycle_linear_graph]

variable {k : Type u} [Field k]
  (f : Spec (.of R[X]) ⟶ Spec (.of k))

/-- The whole pencil as a signed correspondence on the parameter chart. -/
def unitProductPencilCycle [Nontrivial R] (a b : Rˣ) :
    finiteCorrespondences f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) :=
  polynomialCycle f (unitProductPencil a b) (unitProductPencil_monic a b)
    (unitProductPencil_constant_isUnit a b)

variable [IsDomain R] [IsIntegrallyClosed R] [Smooth f] [IsSeparated f] [QuasiCompact f]

local notation "ev₀" => evalRingHom (0 : R)
local notation "ev₁" => evalRingHom (1 : R)
local notation "f₀" => Spec.map (CommRingCat.ofHom ev₀) ≫ f
local notation "f₁" => Spec.map (CommRingCat.ofHom ev₁) ≫ f

/-- The actual graph restriction at zero is the sum of the product graph and
the unit graph. The whole quotient retains repeated roots. -/
theorem unitProductPencilCycle_graphRestriction_zero
    [Smooth f₀] [IsSeparated f₀] [QuasiCompact f₀] (a b : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    graphRestriction f ev₀ (unitProductPencilCycle f a b) =
      unitGraphCycle f₀ (a * b) hR + unitGraphCycle f₀ 1 hR := by
  rw [unitProductPencilCycle, polynomialCycle_graphRestriction]
  exact polynomialCycle_eq_two_unitGraphs f₀ _ _ _ (a * b) 1
    (unitProductPencil_map_eval_zero a b) hR

/-- The actual graph restriction at one is the sum of the two input graphs. -/
theorem unitProductPencilCycle_graphRestriction_one
    [Smooth f₁] [IsSeparated f₁] [QuasiCompact f₁] (a b : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    graphRestriction f ev₁ (unitProductPencilCycle f a b) =
      unitGraphCycle f₁ a hR + unitGraphCycle f₁ b hR := by
  rw [unitProductPencilCycle, polynomialCycle_graphRestriction]
  exact polynomialCycle_eq_two_unitGraphs f₁ _ _ _ a b
    (unitProductPencil_map_eval_one a b) hR

end AlgebraicGeometry.NativeTorusPolynomial
