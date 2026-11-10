/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPGroupDescent
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteScalarBranch

/-!
# Actual complete-DVR coefficient descent to p-group branches

All finite integral closures, uniformizer equations, and branch maps are
constructed. The resulting degree annihilator has no valuation diagram,
ramification, residue compatibility, or multiplicity-count premise.

Adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/CompletePGroupDescent.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. The original
residue-characteristic-zero assumptions, actual coefficient fields and
integral closures are retained. All norm maps are the existing native chosen norms.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

attribute [local instance] scalarBranchAlgebra closureAlgebra

private theorem completeDescent_closureMap_injective
    (A E D : Type*) [CommRing A] [Field E] [Field D]
    [Algebra A E] [Algebra A D] [Algebra E D] [IsScalarTower A E D] :
    Function.Injective (algebraMap (integralClosure A E) (integralClosure A D)) := by
  intro s t h
  apply Subtype.ext
  apply (algebraMap E D).injective
  exact congrArg (fun z : integralClosure A D => (z : D)) h

private theorem completeDescent_exists_positive_ramification_pair
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f)
    {π : A} (hπ : Irreducible π) {ϖ : B} (hϖ : Irreducible ϖ) :
    ∃ eu : ℕ × Bˣ, 0 < eu.1 ∧ f π = (eu.2 : B) * ϖ ^ eu.1 := by
  obtain ⟨e, he, u, hu⟩ := exists_positive_ramification f hf hπ hϖ
  exact ⟨(e, u), he, hu⟩

/-- Actual coefficient extensions whose every branch lies in a p-group ambient
annihilate the complete norm-residue defect by their actual field degree. -/
theorem finrank_smul_norm_residue_difference_complete_of_pGroup_branches
    (R F L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra R L] [IsScalarTower R F L]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d)
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)}, AdjoinRoot (poly r.1.2) →ₐ[L] Ω)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    let _ := (AdjoinRoot.powerBasis' (monic p)).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot (poly p))
    let _ := integralClosure_isLocalHom R F (AdjoinRoot (poly p))
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly p))
      (integralClosure R (AdjoinRoot (poly p)))
    let _ := integralClosure_residue_finite R F (AdjoinRoot (poly p))
    Module.finrank F L •
      (dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) -
        milnorKNorm (ResidueField R)
          (ResidueField (integralClosure R (AdjoinRoot (poly p)))) n
          (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly p)))
            (AdjoinRoot (poly p)) n x)) = 0 := by
  classical
  dsimp only
  let E := AdjoinRoot (poly p)
  let S := integralClosure R E
  let T := integralClosure R L
  let I := {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)}
  let D := fun r : I => AdjoinRoot (poly r.1.2)
  let U := fun r : I => integralClosure R (D r)
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let : FiniteDimensional F E := (AdjoinRoot.powerBasis' (monic p)).finite
  let : ∀ r : I, FiniteDimensional L (D r) := fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  let : ∀ r : I, FiniteDimensional F (D r) := fun r => Module.Finite.trans L (D r)
  let : IsDiscreteValuationRing S := integralClosure_isDiscreteValuationRing R F E
  let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing R F L
  let : ∀ r : I, IsDiscreteValuationRing (U r) := fun r =>
    integralClosure_isDiscreteValuationRing R F (D r)
  let : IsLocalHom (algebraMap R S) := integralClosure_isLocalHom R F E
  let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F L
  let : ∀ r : I, IsLocalHom (algebraMap R (U r)) := fun r =>
    integralClosure_isLocalHom R F (D r)
  let : IsFractionRing S E := IsIntegralClosure.isFractionRing_of_finite_extension R F E S
  let : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  let : ∀ r : I, IsFractionRing (U r) (D r) := fun r =>
    IsIntegralClosure.isFractionRing_of_finite_extension R F (D r) (U r)
  let : Module.Finite R S := IsIntegralClosure.finite R F E S
  let : Module.Finite R T := IsIntegralClosure.finite R F L T
  let : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure_algebraMap_injective R F E)
  let : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure_algebraMap_injective R F L)
  let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete R F L
  let : CharZero (ResidueField T) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField T)).injective
  let : ∀ r : I, IsScalarTower R E (D r) := fun r => CompleteScalarBranch.baseBranchTower R p r
  let : ∀ r : I, Algebra S (U r) := fun r => closureAlgebra R E (D r)
  let : ∀ r : I, Algebra T (U r) := fun r => closureAlgebra R L (D r)
  let : ∀ r : I, IsScalarTower R S (U r) := fun r => baseTower R E (D r)
  let : ∀ r : I, IsScalarTower R T (U r) := fun r => baseTower R L (D r)
  let : ∀ r : I, IsLocalHom (algebraMap S (U r)) := fun r =>
    CompleteScalarBranch.oldRoot_isLocalHom R p r
  let : ∀ r : I, IsLocalHom (algebraMap T (U r)) := fun r =>
    CompleteScalarBranch.coefficient_isLocalHom R p r
  let : ∀ r : I, Module.Finite T (U r) := fun r =>
    CompleteScalarBranch.coefficient_finite R F L p r
  let : ∀ r : I, Module.IsTorsionFree T (U r) := fun r => upper_torsionFree R F L (D r)
  let : ∀ r : I, @IsScalarTower T (U r) (D r) _ _
      (AdjoinRoot.instSMulAdjoinRoot (S := T) (poly r.1.2)) := fun r => by
    let : Algebra T (D r) := AdjoinRoot.instAlgebra (S := T) (poly r.1.2)
    exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ r : I, Algebra T (D r) := fun r =>
    AdjoinRoot.instAlgebra (S := T) (poly r.1.2)
  let : ∀ r : I, IsIntegralClosure (U r) T (D r) := fun r =>
    CompleteScalarBranch.coefficient_isIntegralClosure R p r
  let π : R := (IsDiscreteValuationRing.exists_irreducible R).choose
  have hπ : Irreducible π := (IsDiscreteValuationRing.exists_irreducible R).choose_spec
  let ϖ : S := (IsDiscreteValuationRing.exists_irreducible S).choose
  have hϖ : Irreducible ϖ := (IsDiscreteValuationRing.exists_irreducible S).choose_spec
  let τ : T := (IsDiscreteValuationRing.exists_irreducible T).choose
  have hτ : Irreducible τ := (IsDiscreteValuationRing.exists_irreducible T).choose_spec
  let ρ (r : I) : U r := (IsDiscreteValuationRing.exists_irreducible (U r)).choose
  have hρ (r : I) : Irreducible (ρ r) :=
    (IsDiscreteValuationRing.exists_irreducible (U r)).choose_spec
  have hRS := completeDescent_exists_positive_ramification_pair (algebraMap R S)
    (integralClosure_algebraMap_injective R F E) hπ hϖ
  have hRT := completeDescent_exists_positive_ramification_pair (algebraMap R T)
    (integralClosure_algebraMap_injective R F L) hπ hτ
  let eu : ℕ × Sˣ := hRS.choose
  let av : ℕ × Tˣ := hRT.choose
  have hs (r : I) : Function.Injective (algebraMap S (U r)) :=
    completeDescent_closureMap_injective R E (D r)
  have ht (r : I) : Function.Injective (algebraMap T (U r)) :=
    completeDescent_closureMap_injective R L (D r)
  have hSU (r : I) := completeDescent_exists_positive_ramification_pair
    (algebraMap S (U r)) (hs r) hϖ (hρ r)
  have hTU (r : I) := completeDescent_exists_positive_ramification_pair
    (algebraMap T (U r)) (ht r) hτ (hρ r)
  let bw (r : I) : ℕ × (U r)ˣ := (hSU r).choose
  let cz (r : I) : ℕ × (U r)ˣ := (hTU r).choose
  exact finrank_smul_norm_residue_difference_eq_zero_of_pGroup_branches R S T p
    (fun r => ↥(U r)) Ω ℓ hG g
    (fun r s => (CompleteScalarBranch.oldRoot_closureMap_apply R p r s).symm)
    hπ hϖ hτ ρ hρ eu.2 eu.1 hRS.choose_spec.2 av.2 av.1 hRT.choose_spec.2
    (fun r => (bw r).2) (fun r => (cz r).2) (fun r => (bw r).1) (fun r => (cz r).1)
    (fun r => (hSU r).choose_spec.2) (fun r => (hTU r).choose_spec.2) n x

end Stacks.Chow

end
