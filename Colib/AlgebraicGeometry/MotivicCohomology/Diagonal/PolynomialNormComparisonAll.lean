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

/-!
# Norm and corestriction on the raw diagonal

Strong induction on polynomial degree runs over all characteristic-zero
fields at the fixed weight. Over each Sylow fixed field, the two restrictions
are sums over the same scalar factors, whose root fields embed in the
corresponding Galois p-group extension. Joint Sylow detection gives equality
on the original raw diagonal.

Adapted from `Motivic/Cohomology/Diagonal/PolynomialNormComparisonAll.lean:39-116`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow

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

local instance rootCharZero {F : Type u} [Field F] [CharZero F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : CharZero (AdjoinRoot (poly p)) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot (poly p))).injective

private theorem restriction_comparison_of_pGroup_of_lower_degrees
    {k L Ω : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field Ω]
    [Algebra k L] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω]
    [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (n d : ℕ) {e : ℕ} (p : MonicIrreducibleOfDegree k e) (hd : e ≤ d)
    (hsplit : ((poly p).map (algebraMap k Ω)).Splits)
    (ih : ∀ (A : Type u) [Field A] [CharZero A] {a : ℕ}
      (r : MonicIrreducibleOfDegree A a), a < d → ∀ y : MilnorKTheory (AdjoinRoot (poly r)) n,
        rawSymbol A n (milnorKNorm A (AdjoinRoot (poly r)) n y) =
          corestriction (k := A) n (rawSymbol (AdjoinRoot (poly r)) n y))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    fieldChange (algebraMap k L) n (rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x)) =
      fieldChange (algebraMap k L) n
        (corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x)) := by
  classical
  rw [rawSymbol_fieldChange,
    milnorKTheoryMap_milnorKNorm_polynomial (L := L) n p x,
    fieldChange_corestriction_rawSymbol_polynomial (L := L) n p x]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  obtain ⟨⟨g⟩, hdegree⟩ := AdjoinRoot.nonempty_algHom_branch_of_splits
    (poly p) (ne_zero p) hsplit (poly r.1.2) (irreducible r.1.2) r.2
  have hbranch : r.1.1 ≤ e := by simpa only [natDegree_eq] using hdegree
  exact rawSymbol_polynomialNorm_of_pGroup_of_lower_degrees ℓ hG n d r.1.2
    (hbranch.trans hd) g ih
    (milnorKTheoryMap (AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2) n x)

/-- In every weight the native norm of a literal polynomial root field agrees
with its finite corestriction after the diagonal Milnor symbol. -/
theorem rawSymbol_polynomialNorm {k : Type u} [Field k] [CharZero k]
    (n : ℕ) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    rawSymbol k n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x) := by
  classical
  have main : ∀ a : ℕ, ∀ (A : Type u) [Field A] [CharZero A]
      (r : MonicIrreducibleOfDegree A a) (y : MilnorKTheory (AdjoinRoot (poly r)) n),
        rawSymbol A n (milnorKNorm A (AdjoinRoot (poly r)) n y) =
          corestriction (k := A) n (rawSymbol (AdjoinRoot (poly r)) n y) := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro A _ _ r y
      let Ω := (poly r).SplittingField
      let : IsGalois A Ω := ⟨⟩
      apply DiagonalRestrictionSylow.eq_of_sylow_restrictions A Ω n
      intro ℓ hℓ
      let : Fact ℓ.Prime := ⟨hℓ⟩
      let S : Sylow ℓ (Ω ≃ₐ[A] Ω) := Classical.arbitrary _
      let L := IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[A] Ω))
      let : CharZero L := charZero_of_injective_algebraMap (algebraMap A L).injective
      refine ⟨S, ?_⟩
      apply restriction_comparison_of_pGroup_of_lower_degrees
        (L := L) (Ω := Ω) ℓ (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ S)
        n a r le_rfl (SplittingField.splits (poly r)) ?_ y
      intro B _ _ b s hb z
      exact ih b hb B s z
  exact main d k p x

/-- For the actual finite extension, the original chosen Milnor norm and
finite corestriction agree under the all-weight diagonal Milnor symbol. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PolynomialNormComparisonAll.lean:72-116"
  "adaptation" "Sylow descent compares the native chosen norm with actual finite corestriction"]
theorem rawSymbol_milnorKNorm
    {k E : Type u} [Field k] [CharZero k] [Field E] [CharZero E]
    [Algebra k E] [FiniteDimensional k E] (n : ℕ) (x : MilnorKTheory E n) :
    rawSymbol k n (milnorKNorm k E n x) =
      corestriction (k := k) (E := E) n (rawSymbol E n x) := by
  obtain ⟨_, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation k E
  exact rawSymbol_milnorKNorm_of_presentation n p ε (rawSymbol_polynomialNorm n p) x

end AlgebraicGeometry.MotivicCohomology.DiagonalPolynomialNormComparisonAll
