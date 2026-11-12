/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The polynomial-coordinate section through an actual rational point

Evaluation at the actual first-coordinate value defines a section without changing the
original coordinate tuple. The factorization is an equality of scheme morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
universe u

namespace Polynomial
/-- A rational polynomial point factors through evaluation at its original variable value. -/
theorem algHom_factors_valueEvaluation (E R : Type u) [CommRing E] [CommRing R] [Algebra E R]
    (φ : Polynomial R →ₐ[E] E) :
    φ.toRingHom = (φ.toRingHom.comp C).comp
      (evalRingHom (algebraMap E R (φ X))) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp only [RingHom.comp_apply, coe_evalRingHom, eval_X]
    exact (φ.commutes (φ X)).symm
end Polynomial

namespace AlgebraicGeometry.Scheme
/-- The actual polynomial-coordinate section at the specified scalar. -/
def polynomialValueSection (R : Type u) [CommRing R] (a : R) :
    Spec (.of R) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (evalRingHom a))

/-- Evaluation is a section of the original polynomial structure map. -/
theorem polynomialValueSection_projection (R : Type u) [CommRing R] (a : R) :
    polynomialValueSection R a ≫ Spec.map (CommRingCat.ofHom (C : R →+* Polynomial R)) =
      𝟙 (Spec (.of R)) := by
  rw [polynomialValueSection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simp only [evalRingHom, eval₂RingHom_comp_C]
  exact Spec.map_id (CommRingCat.of R)

/-- The actual rational marking lies on the section at its original first-coordinate value. -/
theorem polynomialPoint_factors_valueSection (E R : Type u) [CommRing E] [CommRing R]
    [Algebra E R] (φ : Polynomial R →ₐ[E] E) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (φ.toRingHom.comp C)) ≫
        polynomialValueSection R (algebraMap E R (φ X)) := by
  rw [polynomialValueSection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (Polynomial.algHom_factors_valueEvaluation E R φ)
end AlgebraicGeometry.Scheme
