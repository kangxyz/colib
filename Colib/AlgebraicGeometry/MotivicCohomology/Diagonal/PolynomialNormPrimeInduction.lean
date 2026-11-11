/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialNormComparison

import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionDegree
import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionMixed
import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.SymbolFieldChange
import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGeneration
import Colib.RingTheory.KTheory.MilnorK.Norm.LowDegree
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Prime-degree induction for the diagonal polynomial norm comparison

Restriction to the actual root field gives only strict lower-degree factors.
A classwise auxiliary extension of coprime degree gives a mixed-symbol expansion
in the literal coefficient image. Applying finite corestriction to each equality
of restrictions annihilates the same difference by two coprime degrees.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped BigOperators

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialNormInduction

open DiagonalCorestriction DiagonalCorestrictionBaseChange DiagonalFieldChange
open DiagonalMilnorSymbol DiagonalSymbolFieldChange
open PresheafWithTransfers

local instance rootIrreducible {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rootFinite {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : FiniteDimensional F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

local instance rootCharZero {F : Type u} [Field F] [CharZero F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : CharZero (AdjoinRoot (poly p)) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot (poly p))).injective

variable {k : Type u} [Field k] [CharZero k]

private theorem rawSymbol_mixed {E : Type u} [Field E] [Algebra k E]
    [FiniteDimensional k E] [CharZero E] (m : ℕ) (a : Fin m → kˣ) (b : Eˣ) :
    rawSymbol k (m + 1) (milnorKNorm k E (m + 1)
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap k E).toMonoidHom ∘ a) b))) =
      corestriction (k := k) (m + 1) (rawSymbol E (m + 1)
        (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap k E).toMonoidHom ∘ a) b))) := by
  let N := Units.map (Algebra.norm k : E →* k) b
  have hn : milnorKNorm k E (m + 1)
      (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap k E).toMonoidHom ∘ a) b)) =
      milnorKTupleSymbol (Fin.snoc a N) := by
    have htuple :
        (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap k E).toMonoidHom ∘ a) b) :
          MilnorKRing E) =
        milnorKRingMap (algebraMap k E) (milnorKSymbolProd k (List.ofFn a)) *
          milnorKSymbol E b := by
      rw [coe_milnorKTupleSymbol, List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
      rw [← List.map_ofFn, milnorKSymbolProd_append, milnorKSymbolProd_singleton]
      exact congrArg (fun z : MilnorKRing E => z * milnorKSymbol E b)
        (milnorKRingMap_milnorKSymbolProd (algebraMap k E) (List.ofFn a)).symm
    apply Subtype.ext
    rw [coe_milnorKNorm, htuple, milnorKNormRing_map_mul, milnorKNormRing_milnorKSymbol,
      coe_milnorKTupleSymbol, List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
      milnorKSymbolProd_append, milnorKSymbolProd_singleton]
    rfl
  let a' : Fin (m + 1) → kˣ := Fin.snoc a 1
  have he : DiagonalCorestrictionMixed.mixedTuple (E := E) (m + 1) a' (Fin.last m) b =
      Fin.snoc (Units.map (algebraMap k E).toMonoidHom ∘ a) b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [DiagonalCorestrictionMixed.mixedTuple, Function.update_self, Fin.snoc_last]
    · simp only [DiagonalCorestrictionMixed.mixedTuple,
        Function.update_of_ne (Fin.castSucc_ne_last j), a', Fin.snoc_castSucc, Function.comp_apply]
  have hk : Function.update a' (Fin.last m) N = Fin.snoc a N := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.update_self, Fin.snoc_last]
    · simp only [Function.update_of_ne (Fin.castSucc_ne_last j), a', Fin.snoc_castSucc]
  rw [hn, rawSymbol_symbol, rawSymbol_symbol, ← he,
    DiagonalCorestrictionMixed.corestriction_graphSymbol_varying, hk]

private theorem rawSymbol_of_mixed_expansion {E : Type u} [Field E] [Algebra k E]
    [FiniteDimensional k E] [CharZero E] (m : ℕ)
    (c : ((Fin m → kˣ) × Eˣ) →₀ ℤ) (x : MilnorKTheory E (m + 1))
    (hc : (c.sum fun ab z => z • milnorKTupleSymbol
      (Fin.snoc (Units.map (algebraMap k E).toMonoidHom ∘ ab.1) ab.2)) = x) :
    rawSymbol k (m + 1) (milnorKNorm k E (m + 1) x) =
      corestriction (k := k) (m + 1) (rawSymbol E (m + 1) x) := by
  rw [← hc]
  simp only [map_finsuppSum, map_zsmul]
  apply Finset.sum_congr rfl
  intro ab _
  exact congrArg (fun z : (motivicRawBaseComplex k (m + 1)).homology ((m + 1 : ℕ) : ℤ) =>
    c ab • z) (rawSymbol_mixed m ab.1 ab.2)

omit [CharZero k] in
private theorem finrank_smul_difference_eq_zero_of_fieldChange_eq
    {L : Type u} [Field L] [Algebra k L] [Module.Finite k L]
    (n : ℕ) (a b : (motivicRawBaseComplex k n).homology n)
    (h : fieldChange (algebraMap k L) n a = fieldChange (algebraMap k L) n b) :
    (Module.finrank k L : ℤ) • (a - b) = 0 := by
  have ht := congrArg (corestriction (k := k) (E := L) n) h
  rw [corestriction_fieldChange, corestriction_fieldChange] at ht
  exact (smul_sub _ _ _).trans (sub_eq_zero.mpr ht)

variable {d : ℕ} (p : MonicIrreducibleOfDegree k d)

/-- The degree-zero comparison follows from the actual degree laws and the native K₀ map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PolynomialNormPrimeInduction.lean:31-44"
  "adaptation" "Degree zero comparison via the norm and corestriction degree formulas"]
theorem rawSymbol_polynomialNorm_zero (x : MilnorKTheory (AdjoinRoot (poly p)) 0) :
    rawSymbol k 0 (milnorKNorm k (AdjoinRoot (poly p)) 0 x) =
      corestriction (k := k) 0 (rawSymbol (AdjoinRoot (poly p)) 0 x) := by
  obtain ⟨z, rfl⟩ := milnorKZeroMap_surjective (AdjoinRoot (poly p)) x
  have hx : milnorKTheoryMap (algebraMap k (AdjoinRoot (poly p))) 0 (milnorKZeroMap k z) =
      milnorKZeroMap (AdjoinRoot (poly p)) z := by
    simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using
      milnorKTransport_milnorKZeroMap (algebraMap k (AdjoinRoot (poly p))) z
  have hn : milnorKNorm k (AdjoinRoot (poly p)) 0 (milnorKZeroMap (AdjoinRoot (poly p)) z) =
      (Module.finrank k (AdjoinRoot (poly p)) : ℤ) • milnorKZeroMap k z := by
    apply (milnorKTheoryZeroAddEquiv k).injective
    rw [milnorKTheoryZeroAddEquiv_milnorKNorm, map_zsmul,
      milnorKTheoryZeroAddEquiv_milnorKZeroMap, milnorKTheoryZeroAddEquiv_milnorKZeroMap,
      Int.zsmul_eq_mul]
  rw [hn, map_zsmul, ← hx, ← rawSymbol_fieldChange, corestriction_fieldChange]

/-- A field containing the original root field kills the discrepancy under the strict
lower-degree comparison in that coefficient field. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PolynomialNormInduction.lean:39-66"
  "adaptation" "Comparison of the complete native branch sums in smaller degrees"]
theorem restriction_comparison_of_lower_degrees
    {L : Type u} [Field L] [CharZero L] [Algebra k L] (n : ℕ)
    (hp : 1 < d) (f : AdjoinRoot (poly p) →ₐ[k] L)
    (ih : ∀ {e : ℕ} (r : MonicIrreducibleOfDegree L e), e < d →
      ∀ y : MilnorKTheory (AdjoinRoot (poly r)) n,
        rawSymbol L n (milnorKNorm L (AdjoinRoot (poly r)) n y) =
          corestriction (k := L) n (rawSymbol (AdjoinRoot (poly r)) n y))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    fieldChange (algebraMap k L) n (rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x)) =
      fieldChange (algebraMap k L) n
        (corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x)) := by
  classical
  let _ := coefficientFactorFintype (algebraMap k L) (poly p) (ne_zero p)
  rw [rawSymbol_fieldChange, milnorKTheoryMap_milnorKNorm_polynomial,
    fieldChange_corestriction_rawSymbol_polynomial]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply ih r.1.2
  by_contra! hge
  have hdeg : ((poly p).map (algebraMap k L)).natDegree ≤ (poly r.1.2).natDegree := by
    simpa only [natDegree_map, natDegree_eq] using hge
  have hq : poly r.1.2 = (poly p).map (algebraMap k L) :=
    Polynomial.eq_of_monic_of_associated (monic r.1.2) ((monic p).map _)
      (associated_of_dvd_of_natDegree_le r.2 ((monic p).map _).ne_zero hdeg)
  have hirr : Irreducible ((poly p).map (algebraMap k L)) := hq ▸ irreducible r.1.2
  apply hirr.not_isRoot_of_natDegree_ne_one
    (by simpa only [natDegree_map, natDegree_eq] using hp.ne')
  change ((poly p).map (algebraMap k L)).IsRoot (f (AdjoinRoot.root (poly p)))
  rw [IsRoot, eval_map, ← aeval_def, aeval_algHom_apply, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self, map_zero]

private theorem degree_smul_comparison_defect_eq_zero (n : ℕ) (hp : 1 < d)
    (ih : ∀ {e : ℕ} (r : MonicIrreducibleOfDegree (AdjoinRoot (poly p)) e), e < d →
      ∀ y : MilnorKTheory (AdjoinRoot (poly r)) n,
        rawSymbol (AdjoinRoot (poly p)) n
            (milnorKNorm (AdjoinRoot (poly p)) (AdjoinRoot (poly r)) n y) =
          corestriction (k := AdjoinRoot (poly p)) n (rawSymbol (AdjoinRoot (poly r)) n y))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    (d : ℤ) • (rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x) -
      corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x)) = 0 := by
  have h := restriction_comparison_of_lower_degrees (p := p) n hp (AlgHom.id k _) ih x
  have ht := congrArg (corestriction (k := k) (E := AdjoinRoot (poly p)) n) h
  rw [corestriction_fieldChange, corestriction_fieldChange] at ht
  have hd : Module.finrank k (AdjoinRoot (poly p)) = d := by
    rw [(AdjoinRoot.powerBasis (ne_zero p)).finrank, AdjoinRoot.powerBasis_dim, natDegree_eq]
  rw [hd] at ht
  rw [smul_sub, ht, sub_self]

private theorem exists_coprime_smul_comparison_defect_eq_zero (hp : d.Prime) (m : ℕ)
    (x : MilnorKTheory (AdjoinRoot (poly p)) (m + 1)) :
    ∃ e : ℕ, d.Coprime e ∧ (e : ℤ) •
      (rawSymbol k (m + 1) (milnorKNorm k (AdjoinRoot (poly p)) (m + 1) x) -
        corestriction (k := k) (m + 1) (rawSymbol (AdjoinRoot (poly p)) (m + 1) x)) = 0 := by
  obtain ⟨_, _, S, hfinite, _, hcop, _, hq, hgen⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion (poly p) (monic p)
      (by simpa only [natDegree_eq] using hp) m x
  let : FiniteDimensional k S := hfinite
  let : CharZero S := charZero_of_injective_algebraMap (algebraMap k S).injective
  let : Fact (Irreducible ((poly p).map (algebraMap k S))) := ⟨hq⟩
  let M := AdjoinRoot ((poly p).map (algebraMap k S))
  let : FiniteDimensional S M := (AdjoinRoot.powerBasis' ((monic p).map _)).finite
  let : CharZero M := charZero_of_injective_algebraMap (algebraMap S M).injective
  let y : MilnorKTheory M (m + 1) := milnorKTheoryMap
    (AdjoinRoot.map (algebraMap k S) (poly p) ((poly p).map (algebraMap k S)) dvd_rfl) (m + 1) x
  dsimp only at hgen
  obtain ⟨c, hc⟩ := hgen
  have hnorm : milnorKTheoryMap (algebraMap k S) (m + 1)
      (milnorKNorm k (AdjoinRoot (poly p)) (m + 1) x) = milnorKNorm S M (m + 1) y :=
    milnorKTheoryMap_milnorKNorm_irreducible (m + 1) p hq x
  have htransfer : fieldChange (algebraMap k S) (m + 1)
      (corestriction (k := k) (m + 1) (rawSymbol (AdjoinRoot (poly p)) (m + 1) x)) =
      corestriction (k := S) (m + 1) (rawSymbol M (m + 1) y) :=
    fieldChange_corestriction_rawSymbol_irreducible (m + 1) p hq x
  have hcompare := rawSymbol_of_mixed_expansion (k := S) (E := M) m c y hc
  have hchange := rawSymbol_fieldChange (algebraMap k S) (m + 1)
    (milnorKNorm k (AdjoinRoot (poly p)) (m + 1) x)
  have hrestricted := hchange.trans
    ((congrArg (rawSymbol S (m + 1)) hnorm).trans (hcompare.trans htransfer.symm))
  refine ⟨Module.finrank k S, ?_, ?_⟩
  · simpa only [natDegree_eq] using hcop
  · exact finrank_smul_difference_eq_zero_of_fieldChange_eq (L := S) (m + 1) _ _ hrestricted

/-- The actual norm comparison in prime degree follows from the strict lower-degree comparison. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PolynomialNormPrimeInduction.lean:46-78"
  "adaptation" "Classwise coprime restriction and the actual root-field degree annihilator"]
theorem rawSymbol_polynomialNorm_prime_of_lower_degrees (n : ℕ) (hp : d.Prime)
    (ih : ∀ {e : ℕ} (r : MonicIrreducibleOfDegree (AdjoinRoot (poly p)) e), e < d →
      ∀ y : MilnorKTheory (AdjoinRoot (poly r)) n,
        rawSymbol (AdjoinRoot (poly p)) n
            (milnorKNorm (AdjoinRoot (poly p)) (AdjoinRoot (poly r)) n y) =
          corestriction (k := AdjoinRoot (poly p)) n (rawSymbol (AdjoinRoot (poly r)) n y))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x) := by
  cases n with
  | zero => exact rawSymbol_polynomialNorm_zero p x
  | succ m =>
    let δ := rawSymbol k (m + 1) (milnorKNorm k (AdjoinRoot (poly p)) (m + 1) x) -
      corestriction (k := k) (m + 1) (rawSymbol (AdjoinRoot (poly p)) (m + 1) x)
    have hd : (d : ℤ) • δ = 0 := degree_smul_comparison_defect_eq_zero p (m + 1) hp.one_lt ih x
    obtain ⟨e, hcop, he⟩ := exists_coprime_smul_comparison_defect_eq_zero p hp m x
    obtain ⟨a, b, hab⟩ := hcop.isCoprime
    apply sub_eq_zero.mp
    change δ = 0
    calc
      δ = (1 : ℤ) • δ := (one_smul ℤ δ).symm
      _ = (a * d + b * e) • δ := by rw [hab]
      _ = 0 := by rw [add_smul, mul_smul, mul_smul, hd, he, smul_zero, smul_zero, add_zero]

end AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialNormInduction
