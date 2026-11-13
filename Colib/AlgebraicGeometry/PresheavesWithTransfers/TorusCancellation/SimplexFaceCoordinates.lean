/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AlgebraicSimplex.Polynomial
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Abel

/-!
# A polynomial coordinate transverse to an original simplex face

Use the deleted barycentric coordinate as the polynomial variable. The
zeroth coordinate of the face absorbs its contribution to the barycentric
sum. The original face homomorphism is evaluation at zero in this chart.
-/

@[expose] public noncomputable section

open scoped BigOperators Polynomial

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R] {n : ℕ} (i : Fin (n + 2))

/-- The coordinate ring of the simplex viewed as a polynomial ring over the face. -/
def facePolynomialProjection : CoordinateRing R (n + 1) →+* (CoordinateRing R n)[X] :=
  lift (Polynomial.C.comp (constant R n))
    (Fin.insertNth i Polynomial.X (fun j =>
      Polynomial.C (coordinate R n j) - if j = 0 then Polynomial.X else 0)) (by
        rw [Fin.sum_univ_succAbove _ i]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
          Finset.sum_sub_distrib, ← map_sum, sum_coordinate, map_one]
        have h : (∑ j : Fin (n + 1), if j = 0 then
            (Polynomial.X : (CoordinateRing R n)[X]) else 0) = Polynomial.X := by simp
        rw [h]
        abel)

/-- The original coordinates on the face, with the deleted coordinate
added to the zeroth one, embed its ring into the full simplex ring. -/
def facePolynomialCoefficients : CoordinateRing R n →+* CoordinateRing R (n + 1) :=
  lift (constant R (n + 1))
    (fun j => coordinate R (n + 1) (i.succAbove j) +
      if j = 0 then coordinate R (n + 1) i else 0) (by
        rw [Finset.sum_add_distrib]
        have h : (∑ j : Fin (n + 1), if j = 0 then coordinate R (n + 1) i else 0) =
            coordinate R (n + 1) i := by simp
        rw [h]
        calc
          _ = coordinate R (n + 1) i + ∑ j, coordinate R (n + 1) (i.succAbove j) :=
            add_comm _ _
          _ = ∑ j, coordinate R (n + 1) j :=
            (Fin.sum_univ_succAbove (coordinate R (n + 1)) i).symm
          _ = 1 := sum_coordinate R (n + 1))

/-- Evaluate the polynomial variable at the original coordinate of the deleted vertex. -/
def facePolynomialInclusion : (CoordinateRing R n)[X] →+* CoordinateRing R (n + 1) :=
  Polynomial.eval₂RingHom (facePolynomialCoefficients R i) (coordinate R (n + 1) i)

@[simp]
theorem facePolynomialProjection_constant (r : R) :
    facePolynomialProjection R i (constant R (n + 1) r) =
      Polynomial.C (constant R n r) := by
  simp [facePolynomialProjection]

@[simp]
theorem facePolynomialProjection_coordinate_self :
    facePolynomialProjection R i (coordinate R (n + 1) i) = Polynomial.X := by
  simp [facePolynomialProjection]

@[simp]
theorem facePolynomialProjection_coordinate_succAbove (j : Fin (n + 1)) :
    facePolynomialProjection R i (coordinate R (n + 1) (i.succAbove j)) =
      Polynomial.C (coordinate R n j) - if j = 0 then Polynomial.X else 0 := by
  simp [facePolynomialProjection]

@[simp]
theorem facePolynomialCoefficients_constant (r : R) :
    facePolynomialCoefficients R i (constant R n r) = constant R (n + 1) r := by
  simp [facePolynomialCoefficients]

@[simp]
theorem facePolynomialCoefficients_coordinate (j : Fin (n + 1)) :
    facePolynomialCoefficients R i (coordinate R n j) =
      coordinate R (n + 1) (i.succAbove j) +
        if j = 0 then coordinate R (n + 1) i else 0 := by
  simp [facePolynomialCoefficients]

private theorem facePolynomialProjection_comp_coefficients :
    (facePolynomialProjection R i).comp (facePolynomialCoefficients R i) = Polynomial.C := by
  refine AlgebraicSimplex.ringHom_ext (R := R) (n := n) (S := (CoordinateRing R n)[X])
    (f := (facePolynomialProjection R i).comp (facePolynomialCoefficients R i))
    (g := (Polynomial.C : CoordinateRing R n →+* (CoordinateRing R n)[X])) ?_ ?_
  · intro r
    simp
  · intro j
    by_cases hj : j = 0 <;> simp [hj]

/-- The two face charts compose to the identity on the polynomial ring. -/
theorem facePolynomialProjection_comp_inclusion :
    (facePolynomialProjection R i).comp (facePolynomialInclusion R i) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro x
    have h := RingHom.congr_fun (facePolynomialProjection_comp_coefficients R i) x
    simpa only [facePolynomialInclusion, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      RingHom.comp_apply, RingHom.id_apply] using h
  · simp [facePolynomialInclusion, Polynomial.coe_eval₂RingHom]

/-- The two face charts compose to the identity on the simplex ring. -/
theorem facePolynomialInclusion_comp_projection :
    (facePolynomialInclusion R i).comp (facePolynomialProjection R i) = RingHom.id _ := by
  apply AlgebraicSimplex.ringHom_ext
  · intro r
    simp [facePolynomialInclusion, Polynomial.coe_eval₂RingHom]
  · intro j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp [facePolynomialInclusion, Polynomial.coe_eval₂RingHom]
    · by_cases hl : l = 0 <;>
        simp [facePolynomialInclusion, Polynomial.coe_eval₂RingHom, hl]

/-- The actual coface is the zero section in this polynomial chart. -/
def facePolynomialEquiv : CoordinateRing R (n + 1) ≃ₐ[R] (CoordinateRing R n)[X] :=
  { RingEquiv.ofRingHom (facePolynomialProjection R i) (facePolynomialInclusion R i)
      (facePolynomialProjection_comp_inclusion R i)
      (facePolynomialInclusion_comp_projection R i) with
    commutes' r := facePolynomialProjection_constant R i r }

/-- The evaluation map in the chart is the original simplicial face homomorphism. -/
theorem face_eq_eval_zero_comp_facePolynomialEquiv :
    face R i = (Polynomial.evalRingHom (0 : CoordinateRing R n)).comp
      (facePolynomialEquiv R i).toRingHom := by
  apply AlgebraicSimplex.ringHom_ext
  · intro r
    change face R i (constant R (n + 1) r) =
      Polynomial.evalRingHom 0 (facePolynomialProjection R i (constant R (n + 1) r))
    simp [face_eq_pullback]
  · intro j
    change face R i (coordinate R (n + 1) j) =
      Polynomial.evalRingHom 0 (facePolynomialProjection R i (coordinate R (n + 1) j))
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp
    · by_cases hl : l = 0 <;> simp [hl]

end AlgebraicSimplex
