module

import Colib.RingTheory.AdjoinRoot.ScalarFactorEquiv
import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

variable {K : Type*} [Field K]

example (f h : K[X]) (hf : f ≠ 0) (hh : h ≠ 0)
    (g : AdjoinRoot f ≃ₐ[K] AdjoinRoot h) :
    ∃ B : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ f} ≃
        {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ h},
      ∃ ε : ∀ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ f},
          AdjoinRoot (poly r.1.2) ≃ₐ[K] AdjoinRoot (poly (B r).1.2),
        ∀ r, (ε r).toRingHom.comp
            (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr r.2)) =
          (Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr (B r).2)).comp g.toRingHom ∧
          (poly r.1.2).natDegree = (poly (B r).1.2).natDegree :=
  exists_factorIndex_algEquiv f h hf hh g

-- The complete target index is reached, and the original degree indices agree.
example (f h : K[X]) (hf : f ≠ 0) (hh : h ≠ 0)
    (g : AdjoinRoot f ≃ₐ[K] AdjoinRoot h) :
    ∃ B : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ f} ≃
        {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ h},
      Function.Surjective B ∧ ∀ r, r.1.1 = (B r).1.1 := by
  obtain ⟨B, ε, hε⟩ := exists_factorIndex_algEquiv f h hf hh g
  refine ⟨B, B.surjective, fun r => ?_⟩
  simpa only [natDegree_eq] using (hε r).2

-- Field coefficients need only nonzero original polynomials, not irreducibility.
example {k : Type*} [Field k] (φ : k →+* K) (p q : k[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    ∃ B : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ} ≃
        {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ q.map φ},
      ∃ ε : ∀ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ},
          AdjoinRoot (poly r.1.2) ≃ₐ[K] AdjoinRoot (poly (B r).1.2),
        ∀ r, (ε r).toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
          (AdjoinRoot.map φ q (poly (B r).1.2) (B r).2).comp e.toRingHom ∧
          (poly r.1.2).natDegree = (poly (B r).1.2).natDegree :=
  exists_scalarFactorIndex_algEquiv φ p q
    (Polynomial.map_ne_zero hp) (Polynomial.map_ne_zero hq) e

-- The actual original-field square and coefficient-field preservation hold
-- simultaneously for every literal factor of the scalar extension.
example {k : Type*} [Field k] (φ : k →+* K) {d t : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k t)
    (e : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly q)) :
    ∃ B : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ (poly p).map φ} ≃
        {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ (poly q).map φ},
      ∃ ε : ∀ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d //
          poly r.2 ∣ (poly p).map φ},
          AdjoinRoot (poly r.1.2) ≃ₐ[K] AdjoinRoot (poly (B r).1.2),
        ∀ r, (∀ x, ε r (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2 x) =
            AdjoinRoot.map φ (poly q) (poly (B r).1.2) (B r).2 (e x)) ∧
          (∀ c : K, ε r (algebraMap K (AdjoinRoot (poly r.1.2)) c) =
            algebraMap K (AdjoinRoot (poly (B r).1.2)) c) ∧
          (poly r.1.2).natDegree = (poly (B r).1.2).natDegree := by
  obtain ⟨B, ε, hε⟩ := exists_scalarFactorIndex_algEquiv φ (poly p) (poly q)
    (Polynomial.map_ne_zero (irreducible p).ne_zero)
    (Polynomial.map_ne_zero (irreducible q).ne_zero) e
  exact ⟨B, ε, fun r => ⟨fun x => DFunLike.congr_fun (hε r).1 x,
    (ε r).commutes, (hε r).2⟩⟩

-- Reuse the existing actual splitting-field embedding at every source factor.
example {k Ω : Type*} [Field k] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q)
    (hsplit : (p.map (algebraMap k Ω)).Splits) :
    ∃ B : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d //
          poly r.2 ∣ p.map (algebraMap k K)} ≃
        {s : Σ d : ℕ, MonicIrreducibleOfDegree K d //
          poly s.2 ∣ q.map (algebraMap k K)},
      ∃ ε : ∀ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d //
          poly r.2 ∣ p.map (algebraMap k K)},
          AdjoinRoot (poly r.1.2) ≃ₐ[K] AdjoinRoot (poly (B r).1.2),
        ∀ r, (ε r).toRingHom.comp
              (AdjoinRoot.map (algebraMap k K) p (poly r.1.2) r.2) =
            (AdjoinRoot.map (algebraMap k K) q (poly (B r).1.2) (B r).2).comp
              e.toRingHom ∧
          Nonempty (AdjoinRoot (poly r.1.2) →ₐ[K] Ω) ∧
          (poly r.1.2).natDegree ≤ p.natDegree := by
  obtain ⟨B, ε, hε⟩ := exists_scalarFactorIndex_algEquiv (algebraMap k K) p q
    (Polynomial.map_ne_zero hp) (Polynomial.map_ne_zero hq) e
  refine ⟨B, ε, fun r => ⟨(hε r).1, ?_⟩⟩
  exact nonempty_algHom_branch_of_splits p hp hsplit
    (poly r.1.2) (irreducible r.1.2) r.2
