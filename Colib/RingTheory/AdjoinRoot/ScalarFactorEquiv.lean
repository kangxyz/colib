/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.FactorIndexEquiv
public import Colib.RingTheory.AdjoinRoot.Map
public import Colib.RingTheory.AdjoinRoot.MapEquiv

/-!
# Complete native factor correspondence under actual algebra equivalences

An equivalence of two actual polynomial quotient algebras matches all their native
monic irreducible factors. The matched quotient fields are equivalent over the
coefficient field, with the original factor maps and the actual degrees retained.
Scalar extension of an original algebra equivalence therefore matches all factors
of the two coefficient-image polynomials and retains both original field maps.

The conclusions use only the existing literal sigma-subtypes and actual quotient
algebras. They supply the bijection, every quotient equivalence, and their proved
squares together; no branch model, chosen coefficient-equivalence definition,
norm comparison, separability, or multiplicity assertion is introduced.

This supplies the algebraic factor correspondence used in
`Aglib/KTheory/MilnorK/Norm/Polynomial/SylowInduction.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`, using the native maximal spectrum and
quotient algebra constructions instead of that source's branch model.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {K : Type*} [Field K]

/-- An actual algebra equivalence matches the complete literal factor indices,
with actual coefficient-preserving quotient equivalences, factor-map squares,
and equality of the actual factor degrees. Nonreduced quotients are allowed. -/
theorem exists_factorIndex_algEquiv (f h : K[X]) (hf : f ≠ 0) (hh : h ≠ 0)
    (g : AdjoinRoot f ≃ₐ[K] AdjoinRoot h) :
    ∃ B : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ f} ≃
        {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ h},
      ∃ ε : ∀ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ f},
          AdjoinRoot (poly r.1.2) ≃ₐ[K] AdjoinRoot (poly (B r).1.2),
        ∀ r, (ε r).toRingHom.comp
            (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2)) =
          (Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr (B r).2)).comp g.toRingHom ∧
          (poly r.1.2).natDegree = (poly (B r).1.2).natDegree := by
  let M : MaximalSpectrum (AdjoinRoot f) ≃ MaximalSpectrum (AdjoinRoot h) :=
    { toFun m := ⟨m.asIdeal.comap g.symm.toRingHom,
        m.isMaximal.comap_bijective _ g.symm.bijective⟩
      invFun m := ⟨m.asIdeal.comap g.toRingHom,
        m.isMaximal.comap_bijective _ g.bijective⟩
      left_inv m := by
        apply MaximalSpectrum.ext
        ext a
        change g.symm (g a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
        rw [AlgEquiv.symm_apply_apply]
      right_inv m := by
        apply MaximalSpectrum.ext
        ext a
        change g (g.symm a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
        rw [AlgEquiv.apply_symm_apply] }
  let B := (maximalFactorIndexEquiv f hf).symm.trans
    (M.trans (maximalFactorIndexEquiv h hh))
  let F (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ f}) :
      AdjoinRoot f →ₐ[K] AdjoinRoot (poly r.1.2) :=
    Ideal.Quotient.factorₐ K (Ideal.span_singleton_le_span_singleton.mpr r.2)
  let H (s : {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ h}) :
      AdjoinRoot h →ₐ[K] AdjoinRoot (poly s.1.2) :=
    Ideal.Quotient.factorₐ K (Ideal.span_singleton_le_span_singleton.mpr s.2)
  have hF (r) : Function.Surjective (F r) :=
    Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr r.2)
  have hH (s) : Function.Surjective (H s) :=
    Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr s.2)
  have hker (r) : RingHom.ker (H (B r)).toRingHom =
      (RingHom.ker (F r).toRingHom).map g.toRingHom := by
    have hm : nativeFactorMaximal h (B r) = M (nativeFactorMaximal f r) :=
      (maximalFactorIndexEquiv h hh).symm_apply_apply _
    change (nativeFactorMaximal h (B r)).asIdeal =
      (nativeFactorMaximal f r).asIdeal.map g.toRingHom
    rw [hm]
    exact Ideal.comap_symm g.toRingEquiv
  let E (r) : (AdjoinRoot f ⧸ RingHom.ker (F r).toRingHom) ≃ₐ[K]
      (AdjoinRoot h ⧸ RingHom.ker (H (B r)).toRingHom) :=
    Ideal.quotientEquivAlg _ _ g (hker r)
  let ε (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ f}) :
      AdjoinRoot (poly r.1.2) ≃ₐ[K] AdjoinRoot (poly (B r).1.2) :=
    (Ideal.quotientKerAlgEquivOfSurjective (hF r)).symm.trans
      ((E r).trans (Ideal.quotientKerAlgEquivOfSurjective (hH (B r))))
  refine ⟨B, ε, fun r => ⟨?_, ?_⟩⟩
  · let eF : (AdjoinRoot f ⧸ RingHom.ker (F r).toRingHom) ≃ₐ[K]
        AdjoinRoot (poly r.1.2) :=
      Ideal.quotientKerAlgEquivOfSurjective (f := F r) (hF r)
    let eH : (AdjoinRoot h ⧸ RingHom.ker (H (B r)).toRingHom) ≃ₐ[K]
        AdjoinRoot (poly (B r).1.2) :=
      Ideal.quotientKerAlgEquivOfSurjective (f := H (B r)) (hH (B r))
    have hpoint (x : AdjoinRoot f) : ε r (F r x) = H (B r) (g x) := by
      have heF : eF.symm (F r x) =
          Ideal.Quotient.mk (RingHom.ker (F r).toRingHom) x :=
        Ideal.quotientKerAlgEquivOfSurjective_symm_apply (f := F r) (hF r) x
      have heE : E r (Ideal.Quotient.mk (RingHom.ker (F r).toRingHom) x) =
          Ideal.Quotient.mk (RingHom.ker (H (B r)).toRingHom) (g x) := rfl
      have heH : eH (Ideal.Quotient.mk (RingHom.ker (H (B r)).toRingHom) (g x)) =
          H (B r) (g x) :=
        Ideal.quotientKerAlgEquivOfSurjective_mk (f := H (B r)) (hH (B r)) (g x)
      change eH (E r (eF.symm (F r x))) = H (B r) (g x)
      exact (congrArg (fun y => eH (E r y)) heF).trans ((congrArg eH heE).trans heH)
    exact RingHom.ext hpoint
  · calc
      (poly r.1.2).natDegree = Module.finrank K (AdjoinRoot (poly r.1.2)) :=
        finrank_quotient_span_eq_natDegree.symm
      _ = Module.finrank K (AdjoinRoot (poly (B r).1.2)) :=
        (ε r).toLinearEquiv.finrank_eq
      _ = (poly (B r).1.2).natDegree := finrank_quotient_span_eq_natDegree

/-- Extending an original algebra equivalence matches every literal scalar
factor, preserving its coefficient field, degree, and original coefficient-factor
map. Only nonvanishing of the coefficient-image polynomials is required. -/
theorem exists_scalarFactorIndex_algEquiv {k : Type*} [CommRing k]
    (φ : k →+* K) (p q : k[X]) (hp : p.map φ ≠ 0) (hq : q.map φ ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    ∃ B : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ} ≃
        {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ q.map φ},
      ∃ ε : ∀ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ},
          AdjoinRoot (poly r.1.2) ≃ₐ[K] AdjoinRoot (poly (B r).1.2),
        ∀ r, (ε r).toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
          (AdjoinRoot.map φ q (poly (B r).1.2) (B r).2).comp e.toRingHom ∧
          (poly r.1.2).natDegree = (poly (B r).1.2).natDegree := by
  obtain ⟨g, hg⟩ := exists_map_algEquiv φ p q e
  obtain ⟨B, ε, hε⟩ := exists_factorIndex_algEquiv (p.map φ) (q.map φ) hp hq g
  have hfactor (a : k[X]) (b : K[X]) (hb : b ∣ a.map φ) (x : AdjoinRoot a) :
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hb) :
          AdjoinRoot (a.map φ) →+* AdjoinRoot b)
          (AdjoinRoot.map φ a (a.map φ) (dvd_refl _) x) =
        AdjoinRoot.map φ a b hb x := by
    obtain ⟨v, rfl⟩ := mk_surjective x
    rw [map_mk, map_mk]
    rfl
  refine ⟨B, ε, fun r => ⟨?_, (hε r).2⟩⟩
  apply RingHom.ext
  intro x
  let F : AdjoinRoot (p.map φ) →+* AdjoinRoot (poly r.1.2) :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2)
  let H : AdjoinRoot (q.map φ) →+* AdjoinRoot (poly (B r).1.2) :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (B r).2)
  change ε r (AdjoinRoot.map φ p (poly r.1.2) r.2 x) =
    AdjoinRoot.map φ q (poly (B r).1.2) (B r).2 (e x)
  calc
    ε r (AdjoinRoot.map φ p (poly r.1.2) r.2 x) =
        ε r (F (AdjoinRoot.map φ p (p.map φ) (dvd_refl _) x)) :=
      congrArg (ε r) (hfactor p (poly r.1.2) r.2 x).symm
    _ = H (g (AdjoinRoot.map φ p (p.map φ) (dvd_refl _) x)) :=
      DFunLike.congr_fun (hε r).1 _
    _ = H (AdjoinRoot.map φ q (q.map φ) (dvd_refl _) (e x)) :=
      congrArg H (DFunLike.congr_fun hg x)
    _ = AdjoinRoot.map φ q (poly (B r).1.2) (B r).2 (e x) :=
      hfactor q (poly (B r).1.2) (B r).2 (e x)

end AdjoinRoot

end
