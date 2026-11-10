/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.Map
public import Colib.RingTheory.AdjoinRoot.MaximalFactors
public import Colib.RingTheory.AdjoinRoot.TensorSwap

/-!
# Literal polynomial branches matched by the actual tensor swap

For each irreducible polynomial branch on one side, the matching literal monic
irreducible polynomial and an equivalence of the original quotient fields are
produced. The equivalence preserves both original field maps on every element.
There is no newly defined branch carrier, field, or coefficient map.

This is the literal-polynomial form of `tensorSwapBranchRingEquiv` and its two
field-map formulas in `Aglib/RingTheory/AdjoinRootTensorBranches.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`. No norm compatibility is assumed or
concluded here; this supplies the geometric branch comparison needed for it.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

private theorem factor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : R[X]) (q : S[X]) (hq : q ∣ p.map φ) (x : AdjoinRoot p) :
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hq) :
        AdjoinRoot (p.map φ) →+* AdjoinRoot q)
        (AdjoinRoot.map φ p (p.map φ) dvd_rfl x) = AdjoinRoot.map φ p q hq x := by
  obtain ⟨a, rfl⟩ := mk_surjective x
  rw [map_mk, map_mk]
  rfl

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)
local notation "pH" => p.map (algebraMap k H)

/-- Every actual irreducible branch has a tensor-matched literal polynomial
quotient field, retaining both original field maps on every element. No split,
normality, separability, characteristic, or norm compatibility hypothesis is used. -/
theorem exists_tensorSwap_polynomial_branch (q : E[X]) (hqirr : Irreducible q)
    (hq : q ∣ hE) :
    ∃ r : H[X], r.Monic ∧ Irreducible r ∧ ∃ hr : r ∣ pH,
      ∃ e : AdjoinRoot q ≃+* AdjoinRoot r,
        (∀ a : E, e (algebraMap E (AdjoinRoot q) a) =
          AdjoinRoot.map (algebraMap k H) p r hr a) ∧
        (∀ b : H, e (AdjoinRoot.map (algebraMap k E) h q hq b) =
          algebraMap H (AdjoinRoot r) b) := by
  let : Fact (Irreducible q) := ⟨hqirr⟩
  let f : AdjoinRoot hE →+* AdjoinRoot q :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hq)
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  let m : MaximalSpectrum (AdjoinRoot hE) :=
    ⟨RingHom.ker f, RingHom.ker_isMaximal_of_surjective f hf⟩
  let eq : (AdjoinRoot hE ⧸ m.asIdeal) ≃+* AdjoinRoot q :=
    f.quotientKerEquivOfSurjective hf
  have heq (x : AdjoinRoot hE) : eq (Ideal.Quotient.mk m.asIdeal x) = f x :=
    RingHom.quotientKerEquivOfSurjective_apply_mk hf x
  obtain ⟨r, hrmonic, hrirr, hr, er, her⟩ :=
    exists_monic_irreducible_quotient_equiv pH
      (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero)
      (tensorSwapMaximalEquiv p h m)
  let e : AdjoinRoot q ≃+* AdjoinRoot r :=
    eq.symm.trans ((tensorSwapQuotientEquiv p h m).trans er)
  have he (x : AdjoinRoot hE) :
      e (f x) = Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hr)
        (tensorSwapEquiv p h x) := by
    rw [← heq x]
    simp only [e, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    rw [tensorSwapQuotientEquiv_mk, her]
  refine ⟨r, hrmonic, hrirr, hr, e, ?_, ?_⟩
  · intro a
    change e (f (algebraMap E (AdjoinRoot hE) a)) = _
    rw [he, tensorSwapEquiv_algebraMap]
    exact factor_map (algebraMap k H) p r hr a
  · intro b
    rw [← factor_map (algebraMap k E) h q hq b]
    change e (f (AdjoinRoot.map (algebraMap k E) h hE dvd_rfl b)) = _
    rw [he, tensorSwapEquiv_map]
    rfl

end AdjoinRoot
