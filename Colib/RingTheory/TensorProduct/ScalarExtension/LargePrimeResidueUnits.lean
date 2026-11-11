/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.TensorProduct.ScalarExtension.LargePrime
public import Colib.FieldTheory.FiniteExtension.Avoidance.ResiduePolynomial

/-!
# The same two prime extensions avoid all residue conditions

The ground-field open and the norms of every member of a finite family of
nonzero residue-field polynomials are multiplied before either extension is
chosen. Each of the same two actual prime extensions keeps the complete scalar
scheme integral, keeps the whole original closed fiber a singleton, and gives
one tuple where every residue polynomial is a unit on its entire evaluation
fiber. No branches or nilpotent structure of those evaluation fibers are removed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u

/-- Two actual prime extensions satisfy a ground open and all finite residue
conditions at once. Exact full degrees and uniqueness of the entire original
marked fiber are retained alongside the whole-fiber unit statements. -/
theorem exists_two_large_prime_scalar_extensions_with_residue_units
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ ι : Type u} [Finite σ] [Finite ι]
    (K : ι → Type u) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    [∀ i, Module.Finite k (K i)]
    (q : MvPolynomial σ k) (hq : q ≠ 0)
    (f : (i : ι) → MvPolynomial σ (K i)) (hf : ∀ i, f i ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, n.Prime ∧ m.Prime ∧ N < n ∧ N < m ∧ n ≠ m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ IsDomain (R ⊗[k] L) ∧
          (∃! y : PrimeSpectrum (R ⊗[k] L),
            PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x) ∧
          ∃ c : σ → L, MvPolynomial.eval₂ (algebraMap k L) c q ≠ 0 ∧
            (let : Algebra (MvPolynomial σ k) L :=
              (MvPolynomial.eval₂Hom (algebraMap k L) c).toAlgebra
             ∀ i, IsUnit
              (1 ⊗ₜ[MvPolynomial σ k] (MvPolynomial.residueCoefficientEquiv k (K i) σ).symm
                (f i) : L ⊗[MvPolynomial σ k] (MvPolynomial σ k ⊗[k] K i))) := by
  classical
  let := Fintype.ofFinite ι
  let e := fun i => MvPolynomial.residueCoefficientEquiv k (K i) σ
  let : ∀ i, IsDomain (MvPolynomial σ k ⊗[k] K i) :=
    fun i => (e i).toMulEquiv.isDomain (MvPolynomial σ (K i))
  let b := fun i => (e i).symm (f i)
  have hb : ∀ i, b i ≠ 0 := by
    intro i h
    exact hf i (by simpa [b] using congrArg (e i) h)
  let Q : ι → MvPolynomial σ k := fun i => Algebra.norm (MvPolynomial σ k) (b i)
  have hQ : ∀ i, Q i ≠ 0 := fun i => Algebra.norm_ne_zero_iff.mpr (hb i)
  have hprod : (∏ i, Q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hQ i
  obtain ⟨n, m, hn, hm, hNn, hNm, hne, hnm, h⟩ :=
    exists_two_large_prime_scalar_extensions k R p x (q * ∏ i, Q i)
      (mul_ne_zero hq hprod) N
  refine ⟨n, m, hn, hm, hNn, hNm, hne, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdegree, hdomain, hunique, c, hc⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  have heval : MvPolynomial.eval₂ (algebraMap k L) c q ≠ 0 ∧
      (MvPolynomial.eval₂Hom (algebraMap k L) c) (∏ i, Q i) ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hc
  refine ⟨hdegree, hdomain, hunique, c, heval.1, ?_⟩
  let : Algebra (MvPolynomial σ k) L :=
    (MvPolynomial.eval₂Hom (algebraMap k L) c).toAlgebra
  dsimp only
  intro i
  apply Algebra.isUnit_of_norm_ne_zero (L := L)
    (B := L ⊗[MvPolynomial σ k] (MvPolynomial σ k ⊗[k] K i))
  rw [Stacks.Norm.norm_tmul_one]
  change (MvPolynomial.eval₂Hom (algebraMap k L) c) (Q i) ≠ 0
  have hnorms := heval.2
  rw [map_prod] at hnorms
  exact Finset.prod_ne_zero_iff.mp hnorms i (Finset.mem_univ i)

end Algebra.TensorProduct
