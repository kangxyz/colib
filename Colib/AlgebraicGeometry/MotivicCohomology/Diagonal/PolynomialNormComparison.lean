/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChange
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorSymbol
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialPointBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenScalarBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# The scalar branch comparisons for polynomial norms and corestriction

The native Milnor norm and the actual finite motivic corestriction have scalar
branch formulas on the same literal quotient fields. The motivic formula is the
signed cycle comparison on tuple generators, extended additively to the native
homogeneous Milnor group.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped BigOperators

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange

open DiagonalCorestriction DiagonalFieldChange DiagonalMilnorSymbol

local instance normRootIrreducible {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance normRootFinite {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : FiniteDimensional F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

local instance normRootCharZero {F : Type u} [Field F] [CharZero F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : CharZero (AdjoinRoot (poly p)) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot (poly p))).injective

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [CharZero k]

/-- All scalar factors of the native polynomial presentation occur in the homogeneous norm. -/
theorem milnorKTheoryMap_milnorKNorm_polynomial (n : ℕ) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    let _ := coefficientFactorFintype (algebraMap k L) (poly p) (ne_zero p)
    milnorKTheoryMap (algebraMap k L) n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
          poly r.2 ∣ (poly p).map (algebraMap k L)},
        milnorKNorm L (AdjoinRoot (poly r.1.2)) n
          (milnorKTheoryMap (AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2) n x) := by
  have hrefl :
      (AlgEquiv.refl : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly p)).toRingEquiv.toRingHom =
        RingHom.id _ := rfl
  simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap, hrefl,
    RingHom.comp_id] using
    milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv (algebraMap k L) p
      (AlgEquiv.refl : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly p)) n x

/-- The actual corestriction of a diagonal Milnor class has the full scalar branch sum. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/MilnorNormBaseChange.lean:35-62"
  "adaptation" "Extension of the actual signed cycle base change from tuple symbols"]
theorem fieldChange_corestriction_rawSymbol_polynomial [CharZero L]
    (n : ℕ) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    let _ := coefficientFactorFintype (algebraMap k L) (poly p) (ne_zero p)
    fieldChange (algebraMap k L) n
        (corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x)) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
          poly r.2 ∣ (poly p).map (algebraMap k L)},
        corestriction (k := L) n (rawSymbol (AdjoinRoot (poly r.1.2)) n
          (milnorKTheoryMap (AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2) n x)) := by
  classical
  let := coefficientFactorFintype (algebraMap k L) (poly p) (ne_zero p)
  have h : (fieldChange (algebraMap k L) n).comp
      ((corestriction (k := k) n).comp (rawSymbol (AdjoinRoot (poly p)) n)) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
          poly r.2 ∣ (poly p).map (algebraMap k L)},
        (corestriction (k := L) n).comp ((rawSymbol (AdjoinRoot (poly r.1.2)) n).comp
          (milnorKTheoryMap (AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2)
            n).toAddMonoidHom) := by
    apply milnorKTheory_addHom_ext
    intro a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply, LinearMap.toAddMonoidHom_coe,
      milnorKTheoryMap_tupleSymbol, rawSymbol_symbol, corestriction_graphSymbol]
    rw [fieldChange_cycleClass,
      pointPushforward_graph_fieldChange_polynomial p a (irreducible p).separable]
    simp only [map_sum, Function.comp_def]
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply, LinearMap.toAddMonoidHom_coe]
    using DFunLike.congr_fun h x

private theorem sum_scalarFactors_of_irreducible (f : L[X]) (hf : f.Monic) (hi : Irreducible f)
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree L e // poly r.2 ∣ f}]
    {A : Type*} [AddCommMonoid A]
    (g : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e // poly r.2 ∣ f} → A) :
    (∑ r, g r) = g ⟨⟨f.natDegree, ⟨f, hf, hi, rfl⟩⟩, dvd_rfl⟩ := by
  classical
  let r₀ : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e // poly r.2 ∣ f} :=
    ⟨⟨f.natDegree, ⟨f, hf, hi, rfl⟩⟩, dvd_rfl⟩
  change (∑ r, g r) = g r₀
  apply Finset.sum_eq_single r₀
  · intro r _ hne
    exfalso
    apply hne
    apply Subtype.ext
    apply sigma_poly_injective
    exact Polynomial.eq_of_monic_of_associated (monic r.1.2) hf
      ((irreducible r.1.2).associated_of_dvd hi r.2)
  · simp

/-- If the coefficient image remains irreducible, restriction of the norm has one term. -/
theorem milnorKTheoryMap_milnorKNorm_irreducible (n : ℕ) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : Irreducible ((poly p).map (algebraMap k L)))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    let _ : Fact (Irreducible ((poly p).map (algebraMap k L))) := ⟨hp⟩
    let _ : FiniteDimensional L (AdjoinRoot ((poly p).map (algebraMap k L))) :=
      (AdjoinRoot.powerBasis' ((monic p).map _)).finite
    milnorKTheoryMap (algebraMap k L) n (milnorKNorm k (AdjoinRoot (poly p)) n x) =
      milnorKNorm L (AdjoinRoot ((poly p).map (algebraMap k L))) n
        (milnorKTheoryMap (AdjoinRoot.map (algebraMap k L) (poly p)
          ((poly p).map (algebraMap k L)) dvd_rfl) n x) := by
  let := coefficientFactorFintype (algebraMap k L) (poly p) (ne_zero p)
  rw [milnorKTheoryMap_milnorKNorm_polynomial,
    sum_scalarFactors_of_irreducible _ ((monic p).map _) hp]
  rfl

/-- If the coefficient image remains irreducible, restriction of corestriction has one term. -/
theorem fieldChange_corestriction_rawSymbol_irreducible [CharZero L] (n : ℕ) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : Irreducible ((poly p).map (algebraMap k L)))
    (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    let _ : Fact (Irreducible ((poly p).map (algebraMap k L))) := ⟨hp⟩
    let _ : Module.Finite L (AdjoinRoot ((poly p).map (algebraMap k L))) :=
      (AdjoinRoot.powerBasis' ((monic p).map _)).finite
    let _ : CharZero (AdjoinRoot ((poly p).map (algebraMap k L))) :=
      charZero_of_injective_algebraMap
        (algebraMap L (AdjoinRoot ((poly p).map (algebraMap k L)))).injective
    fieldChange (algebraMap k L) n
        (corestriction (k := k) n (rawSymbol (AdjoinRoot (poly p)) n x)) =
      corestriction (k := L) n (rawSymbol (AdjoinRoot ((poly p).map (algebraMap k L))) n
        (milnorKTheoryMap (AdjoinRoot.map (algebraMap k L) (poly p)
          ((poly p).map (algebraMap k L)) dvd_rfl) n x)) := by
  let := coefficientFactorFintype (algebraMap k L) (poly p) (ne_zero p)
  rw [fieldChange_corestriction_rawSymbol_polynomial,
    sum_scalarFactors_of_irreducible _ ((monic p).map _) hp]
  rfl

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange
