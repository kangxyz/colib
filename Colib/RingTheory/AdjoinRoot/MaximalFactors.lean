/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Actual maximal quotients of a polynomial algebra

Every maximal ideal of a nonzero polynomial quotient over a field comes from a
unique monic irreducible polynomial divisor. The quotient identification below
uses only the native ideal factor map and quotient-kernel equivalence. No branch
carrier, new field, or renamed residue map is introduced.

This adapts `branchMaximal_surjective`, `branchMaximal_injective`, and
`branchQuotientEquiv` from `Aglib/RingTheory/AdjoinRootScalarBranches.lean` at
revision `52e09db47998f139064acf48a2d3a64494d0dd9a`, using literal polynomials and
the native maximal spectrum rather than its source's separate branch subtype.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k : Type*} [Field k]

/-- A maximal ideal of the whole polynomial quotient is cut out by a unique
literal monic irreducible divisor. -/
theorem existsUnique_monic_irreducible_factor_comap (p : k[X]) (hp : p ≠ 0)
    (m : MaximalSpectrum (AdjoinRoot p)) :
    ∃! q : k[X], q.Monic ∧ Irreducible q ∧ q ∣ p ∧
      Ideal.span {q} = m.asIdeal.comap (mk p) := by
  classical
  let J := m.asIdeal.comap (mk p)
  have hJ : J.IsPrime := Ideal.comap_isPrime _ _
  have hpJ : p ∈ J := by
    change mk p p ∈ m.asIdeal
    rw [mk_self]
    exact m.asIdeal.zero_mem
  have hJ0 : J ≠ ⊥ := by
    intro h
    exact hp (by simpa only [h, Ideal.mem_bot] using hpJ)
  let g := Submodule.IsPrincipal.generator J
  have hg : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime J hJ0
  have hspan : Ideal.span {normalize g} = J :=
    (Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated g)).trans
      (Ideal.span_singleton_generator J)
  have hmonic : (normalize g).Monic := Polynomial.monic_normalize hg.ne_zero
  refine ⟨normalize g, ⟨hmonic,
    (normalize_associated g).irreducible_iff.mpr hg.irreducible, ?_, hspan⟩, ?_⟩
  · apply Ideal.mem_span_singleton.mp
    rwa [hspan]
  · intro q hq
    exact Polynomial.eq_of_monic_of_associated hq.1 hmonic
      (Ideal.span_singleton_eq_span_singleton.mp (hq.2.2.2.trans hspan.symm))

/-- The native factor map at a divisor has the expected literal polynomial
kernel after pullback to the original polynomial ring. -/
theorem ker_factor_comap_mk (p q : k[X]) (hq : q ∣ p) :
    (RingHom.ker (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr hq))).comap (mk p) =
      Ideal.span {q} := by
  ext a
  change mk q a = 0 ↔ a ∈ Ideal.span {q}
  rw [mk_eq_zero, Ideal.mem_span_singleton]

/-- Every actual maximal quotient is an actual monic irreducible polynomial
quotient, and the identification agrees on every whole-algebra element with the
native factor map. The polynomial and comparison are produced, not assumed. -/
theorem exists_monic_irreducible_quotient_equiv (p : k[X]) (hp : p ≠ 0)
    (m : MaximalSpectrum (AdjoinRoot p)) :
    ∃ q : k[X], q.Monic ∧ Irreducible q ∧ ∃ hq : q ∣ p,
      ∃ e : (AdjoinRoot p ⧸ m.asIdeal) ≃+* AdjoinRoot q,
        ∀ x : AdjoinRoot p, e (Ideal.Quotient.mk m.asIdeal x) =
          Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hq) x := by
  obtain ⟨q, ⟨hmonic, hirr, hq, hcomap⟩, _⟩ :=
    existsUnique_monic_irreducible_factor_comap p hp m
  let f : AdjoinRoot p →+* AdjoinRoot q :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hq)
  have hker : m.asIdeal = RingHom.ker f := by
    apply Ideal.comap_injective_of_surjective (mk p) mk_surjective
    exact hcomap.symm.trans (ker_factor_comap_mk p q hq).symm
  let e : (AdjoinRoot p ⧸ m.asIdeal) ≃+* AdjoinRoot q :=
    (Ideal.quotEquivOfEq hker).trans
      (f.quotientKerEquivOfSurjective (Ideal.Quotient.factor_surjective _))
  refine ⟨q, hmonic, hirr, hq, e, ?_⟩
  intro x
  simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

end AdjoinRoot
