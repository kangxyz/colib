/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.ZeroNeighborhood.PencilBasic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Polynomial interpolation for moving into a smaller open

The diagonal times a monic denominator and a monic numerator have the
same degree and the same prescribed value on the old boundary. The two
correction terms are invertible on the additional boundary.

Adapted from `Motivic/Aglib/RingTheory/Polynomial/Interpolation/OpenMovingPair.lean`
and `Motivic/Aglib/RingTheory/Polynomial/ZeroNeighborhood/{Interpolation,Pencil}.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blobs
`6330c1ef67563168089803c562cd62c801e9d0c6`,
`30b1f3dc0ea04e4c1274b9ad3e24da52de9403c9` and
`322039276089a1746ecc5c66c7632e77824d6d33`.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Polynomial.ZeroNeighborhoodInterpolation

variable {R : Type u} [CommRing R]

/-- The genuine polynomial divided difference, defined over the original ring. -/
def dividedDifference (f : R[X]) (a : R) : R[X] := f /ₘ (X - C a)

lemma dividedDifference_mul (f : R[X]) (a : R) :
    (X - C a) * dividedDifference f a = f - C (f.eval a) := by
  have h := modByMonic_add_div f (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  exact eq_sub_of_add_eq' h

/-- Raise the leading degree without changing either prescribed boundary residue. -/
def monicLift (f r : R[X]) (N : ℕ) : R[X] := r + X * f * X ^ N

lemma monicLift_boundary (f r : R[X]) (N : ℕ) : f ∣ monicLift f r N - r := by
  refine ⟨X * X ^ N, ?_⟩
  dsimp only [monicLift]
  ring

lemma monicLift_monic_natDegree [Nontrivial R] (f r : R[X]) (hf : f.Monic)
    (N : ℕ) (hr : r.natDegree ≤ N) :
    (monicLift f r N).Monic ∧ (monicLift f r N).natDegree = f.natDegree + N + 1 := by
  have hm : (X * f * X ^ N).Monic := (monic_X.mul hf).mul (monic_X.pow N)
  have hd : (X * f * X ^ N).natDegree = f.natDegree + N + 1 := by
    rw [Monic.natDegree_mul (monic_X.mul hf) (monic_X.pow N),
      Monic.natDegree_mul monic_X hf, natDegree_X, natDegree_X_pow]
    omega
  have hr' : r.natDegree < (X * f * X ^ N).natDegree := by rw [hd]; omega
  exact ⟨hm.add_of_right (degree_lt_degree hr'),
    (natDegree_add_eq_right_of_natDegree_lt hr').trans hd⟩

lemma pencil_specialize (p q : R[X]) (t : R) :
    (pencil p q).map (evalRingHom t) = C (1 - t) * p + C t * q := by
  simp only [pencil, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    coe_evalRingHom, eval_sub, eval_one, eval_X, Polynomial.map_map]
  have h : (evalRingHom t).comp C = RingHom.id R := by ext; simp
  simp only [h, Polynomial.map_id]

@[simp] lemma pencil_zero (p q : R[X]) : (pencil p q).map (evalRingHom 0) = p := by
  simp [pencil_specialize]

@[simp] lemma pencil_one (p q : R[X]) : (pencil p q).map (evalRingHom 1) = q := by
  simp [pencil_specialize]

lemma pencil_boundary (f p q : R[X]) (hp : f ∣ p - 1) (hq : f ∣ q - 1) :
    f.map C ∣ pencil p q - 1 := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hq
  refine ⟨C (1 - X) * r.map C + C X * s.map C, ?_⟩
  have hr' := congrArg (Polynomial.map C) hr
  have hs' := congrArg (Polynomial.map C) hs
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul] at hr' hs'
  dsimp only [pencil]
  rw [C_sub, C_1]
  linear_combination (1 - C X) * hr' + C X * hs'

/-- The original polynomial boundary coordinate is a unit on the whole family. -/
lemma pencil_boundary_unit (f p q : R[X]) (hp : f ∣ p - 1) (hq : f ∣ q - 1) :
    IsUnit (AdjoinRoot.mk (pencil p q) (f.map C)) := by
  obtain ⟨r, hr⟩ := pencil_boundary f p q hp hq
  have hc : IsCoprime (pencil p q) (f.map C) := by
    refine ⟨1, -r, ?_⟩
    linear_combination hr
  have hu := hc.map (AdjoinRoot.mk (pencil p q))
  simpa only [AdjoinRoot.mk_self, isCoprime_zero_left] using hu

end Polynomial.ZeroNeighborhoodInterpolation

open Polynomial.ZeroNeighborhoodInterpolation

namespace Polynomial.OpenMovingPair
variable {R : Type u} [CommRing R]

/-- The diagonal factor has an actual polynomial inverse modulo the old boundary. -/
theorem exists_diagonal_inverse (f : R[X]) (a : R) (ha : IsUnit (f.eval a)) :
    ∃ r : R[X], f ∣ (X - C a) * r - 1 := by
  obtain ⟨v, hv⟩ := ha
  refine ⟨-C (↑(v⁻¹) : R) * dividedDifference f a, -C (↑(v⁻¹) : R), ?_⟩
  have hd := dividedDifference_mul f a
  have hu : C (↑(v⁻¹) : R) * C (f.eval a) = (1 : R[X]) := by
    rw [← hv, ← C_mul]
    simp
  linear_combination -C (↑(v⁻¹) : R) * hd + hu

/-- Actual CRT interpolation: inverse diagonal on the old boundary, one on the new boundary. -/
theorem exists_boundary_residue (f g : R[X]) (hfg : IsCoprime f g)
    (a : R) (ha : IsUnit (f.eval a)) :
    ∃ r : R[X], f ∣ (X - C a) * r - 1 ∧ g ∣ r - 1 := by
  obtain ⟨r, b, hb⟩ := exists_diagonal_inverse f a ha
  obtain ⟨u, v, huv⟩ := hfg
  refine ⟨r * v * g + u * f, ?_, ?_⟩
  · refine ⟨b * v * g + ((X - C a) - 1) * u, ?_⟩
    linear_combination v * g * hb + huv
  · refine ⟨(r - 1) * v, ?_⟩
    linear_combination huv

/-- Produce both monic endpoints, with the precise degree difference needed for a pencil. -/
theorem exists_monic_pair [Nontrivial R] (f g : R[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : IsCoprime f g) (a : R) (ha : IsUnit (f.eval a)) :
    ∃ d q : R[X], d.Monic ∧ q.Monic ∧ q.natDegree = d.natDegree + 1 ∧
      f ∣ (X - C a) * d - 1 ∧ g ∣ d - 1 ∧ f * g ∣ q - 1 := by
  obtain ⟨r, hr, hrg⟩ := exists_boundary_residue f g hfg a ha
  let N := r.natDegree
  let d := monicLift (f * g) r N
  let q := monicLift (f * g) 1 (N + 1)
  have hd := monicLift_monic_natDegree (f * g) r (hf.mul hg) N le_rfl
  have hq := monicLift_monic_natDegree (f * g) 1 (hf.mul hg) (N + 1) (by simp)
  have hdf : f ∣ d - r := dvd_trans (dvd_mul_right f g) (monicLift_boundary _ _ _)
  have hdg : g ∣ d - r := dvd_trans (dvd_mul_left g f) (monicLift_boundary _ _ _)
  refine ⟨d, q, hd.1, hq.1, ?_, ?_, ?_, monicLift_boundary _ _ _⟩
  · rw [hq.2, hd.2]
    omega
  · convert dvd_add (dvd_mul_of_dvd_right hdf (X - C a)) hr using 1
    ring
  · convert dvd_add hdg hrg using 1
    ring

/-- A Bezout identity forces the entire boundary to be invertible on the whole zero scheme. -/
theorem boundary_unit (p f r : R[X]) (h : f ∣ r * p - 1) :
    IsUnit (AdjoinRoot.mk p f) := by
  obtain ⟨b, hb⟩ := h
  have hc : IsCoprime p f := ⟨r, -b, by linear_combination hb⟩
  simpa only [AdjoinRoot.mk_self, isCoprime_zero_left] using
    hc.map (AdjoinRoot.mk p)

end Polynomial.OpenMovingPair
