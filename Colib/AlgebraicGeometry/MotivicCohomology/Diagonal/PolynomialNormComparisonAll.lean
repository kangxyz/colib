/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialNormPGroupInduction
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.RestrictionSylow
public import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding

import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.SymbolFieldChange
import Colib.FieldTheory.AdjoinRoot.SeparablePresentation
import Colib.FieldTheory.PurelyInseparable.NormalPrimePower
import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeChosenPresentation

/-!
# Norm and corestriction on the raw diagonal

Strong induction on field degree runs over all finite extensions at the fixed
weight. Both maps compose through a proper intermediate field. An inseparable
extension without such a field is purely inseparable of prime degree.
For a separable presentation, the two restrictions to each Sylow fixed field
are sums over the same scalar factors. Joint Sylow detection gives equality.

The Sylow argument adapts
`Motivic/Cohomology/Diagonal/PolynomialNormComparisonAll.lean:39-116`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Module

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialNormComparisonAll

open DiagonalCorestriction DiagonalCorestrictionBaseChange DiagonalFieldChange
open DiagonalMilnorSymbol DiagonalPolynomialNormInduction DiagonalSymbolFieldChange
open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

local instance rootIrreducible {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rootFinite {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) :
    FiniteDimensional F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

private theorem restriction_comparison_of_pGroup_of_lower_degrees
    {k L Ω : Type u} [Field k] [Field L] [Field Ω]
    [Algebra k L] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω]
    [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (n d : ℕ) {e : ℕ} (p : MonicIrreducibleOfDegree k e) (hd : e ≤ d)
    (hsplit : ((poly p).map (algebraMap k Ω)).Splits)
    (ih : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B] [FiniteDimensional A B],
      finrank A B < d → ∀ y : MilnorKTheory B n,
        rawSymbol A n (milnorKNorm A B n y) = corestriction (k := A) n (rawSymbol B n y))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    fieldChange (algebraMap k L) n (rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x)) =
      fieldChange (algebraMap k L) n
        (corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x)) := by
  classical
  rw [rawSymbol_fieldChange,
    milnorKTheoryMap_milnorKNorm_polynomial_weighted (L := L) n p x,
    fieldChange_corestriction_rawSymbol_polynomial_weighted (L := L) n p x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro r _
  obtain ⟨⟨g⟩, hdegree⟩ := AdjoinRoot.nonempty_algHom_branch_of_splits
    (poly p) (ne_zero p) hsplit (poly r.1.2) (irreducible r.1.2) r.2
  have hbranch : r.1.1 ≤ e := by simpa only [natDegree_eq] using hdegree
  exact congrArg (fun z => (multiplicity (poly r.1.2) ((poly p).map (algebraMap k L)) : ℤ) • z)
    (rawSymbol_polynomialNorm_of_pGroup_of_lower_degrees ℓ hG n d r.1.2
      (hbranch.trans hd) g ih
      (milnorKTheoryMap (AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2) n x))

private theorem rawSymbol_separable_polynomialNorm_of_lower_degrees
    {k : Type u} [Field k] (n d : ℕ) {e : ℕ} (p : MonicIrreducibleOfDegree k e)
    (hd : e ≤ d) (hsep : (poly p).Separable)
    (ih : ∀ (A B : Type u) [Field A] [Field B] [Algebra A B] [FiniteDimensional A B],
      finrank A B < d → ∀ y : MilnorKTheory B n,
        rawSymbol A n (milnorKNorm A B n y) = corestriction (k := A) n (rawSymbol B n y))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x) := by
  classical
  let Ω := (poly p).SplittingField
  let : IsGalois k Ω := IsGalois.of_separable_splitting_field hsep
  apply DiagonalRestrictionSylow.eq_of_sylow_restrictions k Ω n
  intro ℓ hℓ
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let S : Sylow ℓ (Ω ≃ₐ[k] Ω) := Classical.arbitrary _
  let L := IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))
  refine ⟨S, ?_⟩
  exact restriction_comparison_of_pGroup_of_lower_degrees
    (L := L) (Ω := Ω) ℓ (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ S)
    n d p hd (SplittingField.splits (poly p)) ih x

/-- For every finite extension, the original chosen Milnor norm and finite
corestriction agree under the all-weight diagonal Milnor symbol. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PolynomialNormComparisonAll.lean:72-116"
  "adaptation" "The separable stage uses the original Sylow norm and corestriction comparison"]
theorem rawSymbol_milnorKNorm
    {k E : Type u} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (n : ℕ) (x : MilnorKTheory E n) :
    rawSymbol k n (milnorKNorm k E n x) =
      corestriction (k := k) (E := E) n (rawSymbol E n x) := by
  classical
  have main : ∀ d : ℕ, ∀ (A B : Type u) [Field A] [Field B] [Algebra A B]
      [FiniteDimensional A B], finrank A B = d → ∀ y : MilnorKTheory B n,
        rawSymbol A n (milnorKNorm A B n y) = corestriction (k := A) n (rawSymbol B n y) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro A B _ _ _ _ hd y
      have lower (C D : Type u) [Field C] [Field D] [Algebra C D] [FiniteDimensional C D]
          (hCD : finrank C D < d) (z : MilnorKTheory D n) :
          rawSymbol C n (milnorKNorm C D n z) = corestriction (k := C) n (rawSymbol D n z) :=
        ih _ hCD C D rfl z
      by_cases hone : finrank A B = 1
      · exact rawSymbol_milnorKNorm_of_finrank_eq_one n hone y
      by_cases hproper : ∃ M : IntermediateField A B, M ≠ ⊥ ∧ M ≠ ⊤
      · obtain ⟨M, hMbot, hMtop⟩ := hproper
        let : FiniteDimensional M B := FiniteDimensional.right A M B
        have hlo : 1 < finrank A M :=
          lt_of_le_of_ne (Nat.succ_le_of_lt finrank_pos)
            (Ne.symm (fun h => hMbot (IntermediateField.finrank_eq_one_iff.mp h)))
        have hup : 1 < finrank M B :=
          lt_of_le_of_ne (Nat.succ_le_of_lt finrank_pos)
            (Ne.symm (fun h => hMtop (IntermediateField.finrank_eq_one_iff_eq_top.mp h)))
        have hlower : finrank A M < d := by
          rw [← hd, ← finrank_mul_finrank A M B, Nat.mul_comm]
          exact lt_mul_of_one_lt_left finrank_pos hup
        have hupper : finrank M B < d := by
          rw [← hd, ← finrank_mul_finrank A M B]
          exact lt_mul_of_one_lt_left finrank_pos hlo
        exact rawSymbol_milnorKNorm_of_tower n (lower A M hlower) (lower M B hupper) y
      by_cases hsep : Algebra.IsSeparable A B
      · let : Algebra.IsSeparable A B := hsep
        obtain ⟨e, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation A B
        have hdegree : finrank A B = e :=
          ε.toLinearEquiv.finrank_eq.trans
            (finrank_quotient_span_eq_natDegree.trans (natDegree_eq p))
        have hpoly : (poly p).Separable :=
          AdjoinRoot.polynomial_separable_of_algHom (poly p) (monic p) ε.symm.toAlgHom
        exact rawSymbol_milnorKNorm_of_presentation n p ε
          (rawSymbol_separable_polynomialNorm_of_lower_degrees n d p
            (hdegree.symm.trans hd).le hpoly lower) y
      have hbot : separableClosure A B = ⊥ := by
        by_contra hbot
        exact hproper ⟨separableClosure A B, hbot,
          fun htop => hsep ((separableClosure.eq_top_iff A B).mp htop)⟩
      let : IsPurelyInseparable A B := separableClosure.eq_bot_iff.mp hbot
      obtain ⟨p, _⟩ := ExpChar.exists A
      obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow A B p
      have hp : p.Prime := (expChar_is_prime_or_one A p).resolve_right fun he =>
        hone (hr.trans (by rw [he, one_pow]))
      let : Fact p.Prime := ⟨hp⟩
      let : CharP A p := (expChar_prime_iff A hp).mp inferInstance
      have hnontrivial : 1 < finrank A B :=
        lt_of_le_of_ne (Nat.succ_le_of_lt finrank_pos) (Ne.symm hone)
      obtain ⟨P, _, hP⟩ :=
        IntermediateField.exists_normal_prime_subfield_of_finrank_pow_embedding
          p r hr (AlgHom.id A B) hnontrivial
      have hPtop : P = ⊤ := by
        by_contra htop
        have hPbot : P ≠ ⊥ := fun hb =>
          hp.ne_one (hP.symm.trans (by rw [hb, IntermediateField.finrank_bot]))
        exact hproper ⟨P, hPbot, htop⟩
      have hpB : Nat.Prime (finrank A B) := by
        rw [hPtop, IntermediateField.finrank_top'] at hP
        rwa [hP]
      obtain ⟨a, _, ε, hdegree, _⟩ :=
        exists_selected_simpleMilnorNorm_presentation_of_prime hpB
      let f := minpolyOfDegree A (Algebra.IsIntegral.isIntegral (R := A) a)
      let e : B ≃ₐ[A] AdjoinRoot (poly f) :=
        { toRingEquiv := ε.toRingEquiv
          commutes' := ε.commutes }
      have hpF : (minpoly A a).natDegree.Prime := hdegree.symm ▸ hpB
      apply rawSymbol_milnorKNorm_of_presentation n f e ?_ y
      intro z
      apply rawSymbol_polynomialNorm_prime_of_lower_degrees (p := f) n hpF ?_ z
      intro b s hb t
      have hrank : finrank (AdjoinRoot (poly f)) (AdjoinRoot (poly s)) = b :=
        finrank_quotient_span_eq_natDegree.trans (natDegree_eq s)
      exact lower (AdjoinRoot (poly f)) (AdjoinRoot (poly s))
        (by rw [hrank, ← hd, ← hdegree]; exact hb) t
  exact main (finrank k E) k E rfl x

/-- The native norm of a literal polynomial root field agrees with its finite
corestriction in every diagonal weight. -/
theorem rawSymbol_polynomialNorm {k : Type u} [Field k]
    (n : ℕ) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x) :=
  rawSymbol_milnorKNorm n x

end AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialNormComparisonAll
