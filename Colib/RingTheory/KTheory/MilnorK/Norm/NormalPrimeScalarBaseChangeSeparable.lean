/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeChosenComparisonSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.SeparableScalarFactors
public import Colib.FieldTheory.Polynomial.PrimeNormalSeparable
public import Colib.FieldTheory.AdjoinRoot.Separable

/-!
# Separable normal-prime scalar base change for the actual chosen norm

Only separability of the original polynomial or extension is required. Coefficient
extensions are arbitrary, including inseparable and transcendental extensions.
Every literal irreducible factor has degree one or the original prime; its actual
root field is normal and separable. These facts identify its existing chosen norm
with its simple norm. The complete factor formula is an unweighted sum because
separability makes every actual multiplicity one.

The branch-field formula uses actual algebra equivalences and commuting ring maps,
not norm-comparison hypotheses. Native finite-dimensionality is supplied by power
bases for the complete scalar-factor formula. No field, norm or map model is added.
-/

@[expose] public noncomputable section

open Polynomial Module

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- Polynomial separability gives separability of the literal native quotient field. -/
theorem isSeparable_quotient_of_polynomial_separable
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) :
    Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p}) := by
  let : Fact (Irreducible (poly p)) := ⟨irreducible p⟩
  exact AdjoinRoot.isSeparable_of_polynomial_separable (poly p) hsep

/-- Degree one or separable normal prime degree identifies the actual chosen norm. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime_of_separable
    {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] [Normal k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hd : d = 1 ∨ d.Prime)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
  rcases hd with hone | hprime
  · exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_degree_one p hone f x
  · have hdim : finrank k L = d := by
      calc
        finrank k L = finrank k (k[X] ⧸ Ideal.span {poly p}) :=
          f.toLinearEquiv.finrank_eq
        _ = (poly p).natDegree := finrank_quotient_span_eq_natDegree
        _ = d := natDegree_eq p
    have hp : Nat.Prime (finrank k L) := by rwa [hdim]
    exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable hp p f x

/-- The native quotient comparison in degree one or separable normal prime degree. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_one_or_normal_prime_of_separable
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hd : d = 1 ∨ d.Prime)
    [FiniteDimensional k (k[X] ⧸ Ideal.span {poly p})]
    [Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p})]
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x = simpleMilnorNorm p x := by
  have h := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime_of_separable
    p hd (AlgEquiv.refl : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k]
      (k[X] ⧸ Ideal.span {poly p})) x
  change milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x =
    simpleMilnorNorm p (milnorKRingMap (RingHom.id _) x) at h
  simpa only [milnorKRingMap_id_apply] using h

/-- Every actual scalar factor has degree one or the original prime in any characteristic. -/
theorem degree_eq_one_or_eq_of_dvd_map_of_normal_prime_of_separable
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    e = 1 ∨ e = d := by
  let : Algebra k K := φ.toAlgebra
  let : Fact (Irreducible (poly p)) := ⟨irreducible p⟩
  let ep : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] AdjoinRoot (poly p) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  let : Normal k (AdjoinRoot (poly p)) := Normal.of_algEquiv ep
  have hp' : (poly p).natDegree.Prime := by simpa only [natDegree_eq p] using hp
  simpa only [natDegree_eq p, natDegree_eq q] using
    Polynomial.natDegree_eq_one_or_eq_of_dvd_map_of_prime_normal_of_separable
      (monic p) (irreducible p) hsep hp' (irreducible q) hq

/-- The actual chosen norm on every coefficient factor is its simple norm.
Normality, separability and the degree alternative are proved from the source. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_dvd_map_of_normal_prime_of_separable
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ)
    [FiniteDimensional K (K[X] ⧸ Ideal.span {poly q})]
    (x : MilnorKRing (K[X] ⧸ Ideal.span {poly q})) :
    milnorKNormRing K (K[X] ⧸ Ideal.span {poly q}) x = simpleMilnorNorm q x := by
  let : Algebra.IsSeparable K (K[X] ⧸ Ideal.span {poly q}) :=
    isSeparable_quotient_of_polynomial_separable q ((hsep.map (f := φ)).of_dvd hq)
  let : Normal K (K[X] ⧸ Ideal.span {poly q}) :=
    normal_quotient_of_dvd_map_of_normal φ p q hq
  have hdegree : e = 1 ∨ e.Prime := by
    rcases degree_eq_one_or_eq_of_dvd_map_of_normal_prime_of_separable φ p hsep hp q hq with h | h
    · exact Or.inl h
    · exact Or.inr (h.symm ▸ hp)
  exact milnorKNormRing_eq_simpleMilnorNorm_of_one_or_normal_prime_of_separable q hdegree x

/-- Base change over the complete literal coefficient-factor subtype. Every factor
occurs once, and every finite-dimensional instance comes from its native power basis. -/
theorem milnorKNormRing_map_eq_sum_scalarFactors_of_normal_prime_of_separable
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hsep : (poly p).Separable) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    let : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
        poly r.2 ∣ (poly p).map φ},
        FiniteDimensional K (K[X] ⧸ Ideal.span {poly r.1.2}) :=
      fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        milnorKNormRing K (K[X] ⧸ Ideal.span {poly r.1.2})
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2) x) := by
  classical
  let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
    (AdjoinRoot.powerBasis' (monic p)).finite
  let : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ},
      FiniteDimensional K (K[X] ⧸ Ideal.span {poly r.1.2}) :=
    fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  let : Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p}) :=
    isSeparable_quotient_of_polynomial_separable p hsep
  change milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) = _
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_normal_prime_of_separable p hp x]
  apply (simpleMilnorNorm_map_eq_sum_scalarFactors_of_separable φ p hsep x).trans
  apply Finset.sum_congr rfl
  intro r _
  exact (milnorKNormRing_eq_simpleMilnorNorm_of_dvd_map_of_normal_prime_of_separable
    φ p hsep hp r.1.2 r.2 _).symm

/-- The unweighted complete scalar-factor sum on actual branch fields.
Only structural quotient equivalences and their actual commuting maps are supplied. -/
theorem milnorKNormRing_map_eq_sum_of_branch_equivs_of_normal_prime_of_separable
    {ι : Type v} (φ : k →+* K)
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Normal k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i))
    (M : ι → Type u) [∀ i, Field (M i)] [∀ i, Algebra K (M i)]
    [∀ i, FiniteDimensional K (M i)]
    (g : ∀ i, M i ≃ₐ[K] (K[X] ⧸ Ideal.span {poly (q i)}))
    (j : ∀ i, L →+* M i)
    (hsquare : ∀ i, (g i).toRingHom.comp (j i) =
      (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)).comp f.toRingHom)
    (x : MilnorKRing L) :
    milnorKRingMap φ (milnorKNormRing k L x) =
      ∑ i ∈ S, milnorKNormRing K (M i) (milnorKRingMap (j i) x) := by
  let : Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p}) :=
    isSeparable_quotient_of_polynomial_separable p hsep
  let : Algebra.IsSeparable k L := AlgEquiv.Algebra.isSeparable f.symm
  let : Normal k (k[X] ⧸ Ideal.span {poly p}) := Normal.of_algEquiv f
  have hdim : finrank k L = d := by
    calc
      finrank k L = finrank k (k[X] ⧸ Ideal.span {poly p}) :=
        f.toLinearEquiv.finrank_eq
      _ = (poly p).natDegree := finrank_quotient_span_eq_natDegree
      _ = d := natDegree_eq p
  have hpL : Nat.Prime (finrank k L) := by rwa [hdim]
  have hsource : milnorKNormRing k L x =
      simpleMilnorNorm p (milnorKRingMap f.toRingHom x) :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable hpL p f x
  have hbranch (i : ι) :
      milnorKNormRing K (M i) (milnorKRingMap (j i) x) =
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i))
            (milnorKRingMap f.toRingHom x)) := by
    let : Normal K (K[X] ⧸ Ideal.span {poly (q i)}) :=
      normal_quotient_of_dvd_map_of_normal φ p (q i) (hq i)
    let : Normal K (M i) := Normal.of_algEquiv (g i).symm
    let : Algebra.IsSeparable K (K[X] ⧸ Ideal.span {poly (q i)}) :=
      isSeparable_quotient_of_polynomial_separable (q i)
        ((hsep.map (f := φ)).of_dvd (hq i))
    let : Algebra.IsSeparable K (M i) := AlgEquiv.Algebra.isSeparable (g i).symm
    have hdegree : e i = 1 ∨ (e i).Prime := by
      rcases degree_eq_one_or_eq_of_dvd_map_of_normal_prime_of_separable
          φ p hsep hp (q i) (hq i) with h | h
      · exact Or.inl h
      · exact Or.inr (h.symm ▸ hp)
    calc
      milnorKNormRing K (M i) (milnorKRingMap (j i) x) =
          simpleMilnorNorm (q i)
            (milnorKRingMap (g i).toRingHom (milnorKRingMap (j i) x)) :=
        milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime_of_separable
          (q i) hdegree (g i) (milnorKRingMap (j i) x)
      _ = _ := by
        let a : (k[X] ⧸ Ideal.span {poly p}) →+*
            (K[X] ⧸ Ideal.span {poly (q i)}) :=
          AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)
        let s : L →+* (k[X] ⧸ Ideal.span {poly p}) := f.toRingHom
        let t : M i →+* (K[X] ⧸ Ideal.span {poly (q i)}) := (g i).toRingHom
        have hc : t.comp (j i) = a.comp s := hsquare i
        have hleft : milnorKRingMap t (milnorKRingMap (j i) x) =
            milnorKRingMap (t.comp (j i)) x :=
          milnorKRingMap_comp_apply (j i) t x
        have hmiddle : milnorKRingMap (t.comp (j i)) x =
            milnorKRingMap (a.comp s) x :=
          congrArg (fun h : L →+* (K[X] ⧸ Ideal.span {poly (q i)}) =>
            milnorKRingMap h x) hc
        have hright : milnorKRingMap a (milnorKRingMap s x) =
            milnorKRingMap (a.comp s) x :=
          milnorKRingMap_comp_apply s a x
        exact congrArg (simpleMilnorNorm (q i))
          (hleft.trans (hmiddle.trans hright.symm))
  calc
    milnorKRingMap φ (milnorKNormRing k L x) =
        milnorKRingMap φ (simpleMilnorNorm p (milnorKRingMap f.toRingHom x)) :=
      congrArg (milnorKRingMap φ) hsource
    _ = ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i))
            (milnorKRingMap f.toRingHom x)) :=
      simpleMilnorNorm_map_eq_weighted_sum_of_factors
        φ p (milnorKRingMap f.toRingHom x) S e q hinj hq hcover
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [multiplicity_eq_one_of_separable_map φ p (q i) hsep (hq i),
        Nat.cast_one, one_zsmul]
      exact (hbranch i).symm

end Stacks.Chow

end
