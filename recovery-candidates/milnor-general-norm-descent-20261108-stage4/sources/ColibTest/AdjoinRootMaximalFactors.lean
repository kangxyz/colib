module

import Colib.RingTheory.AdjoinRoot.MaximalFactors

open Polynomial

variable {k : Type*} [Field k]

-- Nonreduced polynomial algebras are included: only p != 0 is required.
example (p : k[X]) (hp : p ≠ 0) (m : MaximalSpectrum (AdjoinRoot p)) :
    ∃! q : k[X], q.Monic ∧ Irreducible q ∧ q ∣ p ∧
      Ideal.span {q} = m.asIdeal.comap (AdjoinRoot.mk p) :=
  AdjoinRoot.existsUnique_monic_irreducible_factor_comap p hp m

example (p q : k[X]) (hq : q ∣ p) :
    (RingHom.ker (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr hq))).comap (AdjoinRoot.mk p) =
      Ideal.span {q} :=
  AdjoinRoot.ker_factor_comap_mk p q hq

-- The original polynomial and comparison map are conclusions, not extra inputs.
example (p : k[X]) (hp : p ≠ 0) (m : MaximalSpectrum (AdjoinRoot p)) :
    ∃ q : k[X], q.Monic ∧ Irreducible q ∧ ∃ hq : q ∣ p,
      ∃ e : (AdjoinRoot p ⧸ m.asIdeal) ≃+* AdjoinRoot q,
        ∀ x : AdjoinRoot p, e (Ideal.Quotient.mk m.asIdeal x) =
          Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hq) x :=
  AdjoinRoot.exists_monic_irreducible_quotient_equiv p hp m
