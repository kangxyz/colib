/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Regular.SMul

/-! # Interchanging regular principal cuts -/

@[expose] public section

namespace Ideal

section Surjective

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Pulling back a principal cut along a surjection adds its equation to the kernel. -/
theorem ker_quotient_mk_comp_of_surjective (f : A →+* B)
    (hf : Function.Surjective f) (s : A) :
    RingHom.ker ((Quotient.mk (span {f s})).comp f) = RingHom.ker f ⊔ span {s} := by
  rw [← RingHom.comap_ker, mk_ker]
  have h : (span ({s} : Set A)).map f = span {f s} := by
    rw [map_span, Set.image_singleton]
  rw [← h, comap_map_of_surjective f hf, sup_comm, RingHom.ker_eq_comap_bot]

end Surjective

variable {A : Type*} [CommRing A] [IsDomain A]

/-- A regular parameter modulo a principal equation follows from regularity
of that equation modulo the parameter in the opposite order. -/
theorem isSMulRegular_quotient_span_singleton_swap (c s : A) (hc : c ≠ 0)
    (hreg : IsSMulRegular (A ⧸ span {c}) s) :
    IsSMulRegular (A ⧸ span {s}) c := by
  let C : Ideal A := span {c}
  let S : Ideal A := span {s}
  intro u v h
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective v
  change Quotient.mk S c * Quotient.mk S x = Quotient.mk S c * Quotient.mk S y at h
  have hz : Quotient.mk S (c * (x - y)) = 0 := by
    rw [map_mul, map_sub, mul_sub, h, sub_self]
  obtain ⟨d, hd⟩ := mem_span_singleton.mp (Quotient.eq_zero_iff_mem.mp hz)
  have hsd : Quotient.mk C s * Quotient.mk C d = Quotient.mk C s * 0 := by
    rw [mul_zero, ← map_mul, ← hd, map_mul,
      Quotient.eq_zero_iff_mem.mpr (subset_span (Set.mem_singleton c)), zero_mul]
  have hdz : Quotient.mk C d = 0 := hreg hsd
  obtain ⟨e, he⟩ := mem_span_singleton.mp (Quotient.eq_zero_iff_mem.mp hdz)
  have hxy : x - y = s * e := by
    apply mul_left_cancel₀ hc
    rw [hd, he]
    exact mul_left_comm s c e
  apply sub_eq_zero.mp
  rw [← map_sub, Quotient.eq_zero_iff_mem, mem_span_singleton, hxy]
  exact dvd_mul_right s e

end Ideal
