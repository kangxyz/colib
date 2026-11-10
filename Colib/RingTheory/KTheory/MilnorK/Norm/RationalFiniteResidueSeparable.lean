/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalInertResidueSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalSplitResidueSeparable
public import Colib.FieldTheory.Polynomial.PrimeNormalSeparable

/-!
# The complete finite residue square for a separable normal-prime constant norm

The actual constant polynomial over the original closed-point field is either
irreducible or split. In the inert case the original finite local root DVR and
its proved quotient dictionaries give the square. In the split case the original
Galois trace and complete branch permutation give the square. Both formulas use
exactly the original tensor-swap factor index, quotient equivalence and simple norm.
No separability of any auxiliary closed point or top polynomial is required.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  rationalInert_nativeMonic rationalInert_nativeIrreducible rationalInert_rootFinite
  rationalInert_rationalFinite

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)

include hsep hp

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

/-- The original finite residue is the complete native tensor-swap sum, in every
homogeneous degree, including inseparable auxiliary closed points. -/
theorem monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_separable
    (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E))
    (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      ∑ i ∈ S.attach,
        let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
            poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (milnorKRingMap
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) := by
  rcases Polynomial.Monic.irreducible_map_or_splits_of_prime_normal_of_separable
      (K := H) (monic p) (irreducible p) hsep (by rw [natDegree_eq p]; exact hp) with
    hinert | hsplit
  · let : Fact (Irreducible ((poly p).map (algebraMap k H))) := ⟨hinert⟩
    exact monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_inert
      p h hsep hp S hS n x
  · obtain ⟨a, ha⟩ := hsplit.exists_eval_eq_zero
      (Polynomial.degree_ne_of_natDegree_ne (by
        rw [(monic p).natDegree_map, natDegree_eq p]
        exact hp.ne_zero))
    let f : E →ₐ[k] H := AdjoinRoot.liftAlgHom (poly p) (Algebra.ofId k H) a
      (by simpa only [Algebra.toRingHom_ofId, Polynomial.eval_map] using ha)
    exact monicIrreducibleResidue_milnorKNormRing_ratFunc_eq_sum_tensorSwap_of_split
      p hsep hp h f S hS (x : MilnorKRing (RatFunc E))

/-- An exact finite factor set exists and works for every homogeneous degree
and every original rational Milnor class. -/
theorem exists_finset_monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_separable :
    ∃ (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E)),
      ∀ (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)),
        monicIrreducibleResidue h
            (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x :
              MilnorKRing (RatFunc k)) =
          ∑ i ∈ S.attach,
            let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
                poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
            let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
            simpleMilnorNorm r.1.2
              (milnorKRingMap
                ((AdjoinRoot.tensorSwapFactorQuotientEquiv
                  (poly p) (poly h) q).toRingHom :
                    (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                      (H[X] ⧸ Ideal.span {poly r.1.2}))
                (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) := by
  obtain ⟨S, hS⟩ :=
    exists_finset_mem_iff_dvd_map (algebraMap k E) (poly h) (ne_zero h)
  exact ⟨S, hS,
    monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_separable p hsep hp h S hS⟩

end Stacks.Chow
