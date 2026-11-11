/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePGroupFinite
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRWeightedBaseChangeFinite
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRRestrictionKernel
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteScalarBranch
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation
public import Colib.RingTheory.AdjoinRoot.TensorScalarFactors
public import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding
public import Colib.FieldTheory.SylowFixedField

/-!
# Native norm-residue compatibility over a complete DVR

The separable case compares the ramification-weighted generic and residue
branch sums after extension to each Sylow fixed field. The original
maximal separable subfield then reduces an arbitrary finite extension to
the separable case and the purely inseparable tower.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower
open scoped TensorProduct

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib
attribute [local instance] AdjoinRoot.scalarBranchAlgebra closureAlgebra

universe u

/-- The monic power basis supplies finiteness of each actual quotient field. -/
local instance completeFiniteRoot {k : Type u} [Field k] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) : FiniteDimensional k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

private theorem completeFinite_closureMap_injective
    (R E D : Type*) [CommRing R] [Field E] [Field D]
    [Algebra R E] [Algebra R D] [Algebra E D] [IsScalarTower R E D] :
    Function.Injective (algebraMap (integralClosure R E) (integralClosure R D)) := by
  intro s t h
  apply Subtype.ext
  apply (algebraMap E D).injective
  exact congrArg (fun z : integralClosure R D => (z : D)) h

private theorem completeFinite_ramification_pair
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f)
    {π : A} (hπ : Irreducible π) {ρ : B} (hρ : Irreducible ρ) :
    ∃ eu : ℕ × Bˣ, f π = (eu.2 : B) * ρ ^ eu.1 := by
  obtain ⟨e, _, u, hu⟩ := exists_positive_ramification f hf hπ hρ
  exact ⟨(e, u), hu⟩

private theorem completeFinite_compare_branch
    (S T U E L D : Type u)
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Field L] [Algebra T L] [IsFractionRing T L]
    [Field D] [Algebra U D] [IsFractionRing U D]
    [Algebra L D] [FiniteDimensional L D]
    [Algebra T U] [Module.Finite T U] [IsLocalHom (algebraMap T U)]
    (j : S →+* U) [IsLocalHom j] (f : E →+* D)
    (hf : ∀ s, f (algebraMap S E s) = algebraMap U D (j s))
    {ϖ : S} {ρ : U} (hϖ : Irreducible ϖ) (hρ : Irreducible ρ)
    (w : Uˣ) (b : ℕ) (hb : j ϖ = (w : U) * ρ ^ b)
    (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hnorm : dvrMilnorTameSymbol' T L n
        (milnorKNorm L D (n + 1) (milnorKTheoryMap f (n + 1) x)) =
      milnorKNorm (ResidueField T) (ResidueField U) n
        (dvrMilnorTameSymbol' U D n (milnorKTheoryMap f (n + 1) x))) :
    dvrMilnorTameSymbol' T L n
        (milnorKNorm L D (n + 1) (milnorKTheoryMap f (n + 1) x)) =
      b • milnorKNorm (ResidueField T) (ResidueField U) n
        (milnorKTransport (ResidueField.map j) n (dvrMilnorTameSymbol' S E n x)) := by
  have hram := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified j f hf hϖ hρ w b hb n) x
  change dvrMilnorTameSymbol' U D n (milnorKTheoryMap f (n + 1) x) =
    (b : ℤ) • milnorKTheoryMap (ResidueField.map j) n (dvrMilnorTameSymbol' S E n x) at hram
  refine hnorm.trans ?_
  simpa only [natCast_zsmul, map_nsmul, milnorKTheoryMap_eq_transport,
    AddMonoidHom.coe_toIntLinearMap] using
    congrArg (milnorKNorm (ResidueField T) (ResidueField U) n) hram

private theorem completeFinite_defect_of_restriction
    (R T F L : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
    [IsLocalHom (algebraMap R T)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    [Algebra T L] [IsScalarTower R T L] [IsFractionRing T L]
    {π : R} {τ : T} (hπ : Irreducible π) (hτ : Irreducible τ)
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (n : ℕ) (x y : MilnorKTheory (ResidueField R) n) (z : MilnorKTheory (ResidueField T) n)
    (hx : a • milnorKTheoryMap (ResidueField.map (algebraMap R T)) n x = z)
    (hy : a • milnorKTransport (algebraMap (ResidueField R) (ResidueField T)) n y = z) :
    Module.finrank F L • (x - y) = 0 := by
  have hres : algebraMap (ResidueField R) (ResidueField T) =
      ResidueField.map (algebraMap R T) := by
    ext t
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective t
    rfl
  have h : a • milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n x =
      a • milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n y := by
    simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap, ← hres]
      using hx.trans hy.symm
  apply finrank_smul_eq_zero_of_ramified_residue_restrict R T F L hπ hτ v a ha n
  rw [map_sub, smul_sub, h, sub_self]

private abbrev CompleteFiniteFactor {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) (L : Type u) [Field L] [Algebra F L] : Type u :=
  {r : Σ e : ℕ, MonicIrreducibleOfDegree L e // poly r.2 ∣ (poly p).map (algebraMap F L)}

section SeparableRoot

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d)

private theorem completeFinite_separable_norm_baseChange
    (hsep : (poly p).Separable) [Fintype (CompleteFiniteFactor p L)]
    (m : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) m) :
    milnorKTheoryMap (algebraMap F L) m (milnorKNorm F (AdjoinRoot (poly p)) m x) =
      ∑ r : CompleteFiniteFactor p L, milnorKNorm L (AdjoinRoot (poly r.1.2)) m
        (milnorKTheoryMap
          (AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2) m x) := by
  classical
  have hmult (r : CompleteFiniteFactor p L) :
      multiplicity (poly r.1.2) ((poly p).map (algebraMap F L)) = 1 := by
    have hq := (irreducible r.1.2).not_isUnit
    have hs : Squarefree ((poly p).map (algebraMap F L)) := hsep.map.squarefree
    have hne : (poly p).map (algebraMap F L) ≠ 0 := ((monic p).map _).ne_zero
    apply Nat.le_antisymm
    · apply multiplicity_le_of_emultiplicity_le
      exact ((squarefree_iff_emultiplicity_le_one _).mp hs (poly r.1.2)).resolve_right hq
    · exact Nat.succ_le_of_lt (multiplicity_pos_of_dvd r.2
        (FiniteMultiplicity.of_not_isUnit hq hne))
  have hid :
      (AlgEquiv.refl : AdjoinRoot (poly p) ≃ₐ[F] AdjoinRoot (poly p)).toRingEquiv.toRingHom =
        RingHom.id _ := rfl
  simpa only [hmult, Nat.cast_one, one_zsmul, milnorKTheoryMap_eq_transport,
    AddMonoidHom.coe_toIntLinearMap, hid, RingHom.comp_id] using
    (milnorKNorm_map_eq_weighted_sum_scalarFactors_of_finite (algebraMap F L) p
      (AlgEquiv.refl : AdjoinRoot (poly p) ≃ₐ[F] AdjoinRoot (poly p)) m x)

private theorem completeFinite_root_defect_annihilation
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra R F] [IsFractionRing R F]
    [FiniteDimensional F L] [Algebra R L] [IsScalarTower R F L]
    (hsep : (poly p).Separable)
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : CompleteFiniteFactor p L, AdjoinRoot (poly r.1.2) →ₐ[L] Ω)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    let _ := integralClosure_isDiscreteValuationRing_of_finite R F (AdjoinRoot (poly p))
    let _ := integralClosure_isLocalHom R F (AdjoinRoot (poly p))
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly p))
      (integralClosure R (AdjoinRoot (poly p)))
    let _ := integralClosure_residue_finite_of_finite R F (AdjoinRoot (poly p))
    Module.finrank F L •
      (dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) -
        milnorKNorm (ResidueField R)
          (ResidueField (integralClosure R (AdjoinRoot (poly p)))) n
          (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly p)))
            (AdjoinRoot (poly p)) n x)) = 0 := by
  classical
  dsimp only
  let I := CompleteFiniteFactor p L
  let E := AdjoinRoot (poly p)
  let S := integralClosure R E
  let T := integralClosure R L
  let D (r : I) := AdjoinRoot (poly r.1.2)
  let U (r : I) := integralClosure R (D r)
  let : Fintype I := coefficientFactorFintype (algebraMap F L) (poly p) (ne_zero p)
  let : FiniteDimensional F E := (AdjoinRoot.powerBasis' (monic p)).finite
  let : ∀ r, FiniteDimensional L (D r) := fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  let : ∀ r, FiniteDimensional F (D r) := fun r => Module.Finite.trans L (D r)
  let : IsDiscreteValuationRing S := integralClosure_isDiscreteValuationRing_of_finite R F E
  let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing_of_finite R F L
  let : ∀ r, IsDiscreteValuationRing (U r) := fun r =>
    integralClosure_isDiscreteValuationRing_of_finite R F (D r)
  let : IsLocalHom (algebraMap R S) := integralClosure_isLocalHom R F E
  let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F L
  let : ∀ r, IsLocalHom (algebraMap R (U r)) := fun r =>
    integralClosure_isLocalHom R F (D r)
  let : IsFractionRing S E := IsIntegralClosure.isFractionRing_of_finite_extension R F E S
  let : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  let : ∀ r, IsFractionRing (U r) (D r) := fun r =>
    IsIntegralClosure.isFractionRing_of_finite_extension R F (D r) (U r)
  let : Module.Finite R S := integralClosure_finite_of_finite R F E
  let : Module.Finite R T := integralClosure_finite_of_finite R F L
  let : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure_algebraMap_injective R F E)
  let : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure_algebraMap_injective R F L)
  let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete_of_finite R F L
  let : ∀ r, IsScalarTower R E (D r) := fun r => CompleteScalarBranch.baseBranchTower R p r
  let : ∀ r, Algebra S (U r) := fun r => closureAlgebra R E (D r)
  let : ∀ r, Algebra T (U r) := fun r => closureAlgebra R L (D r)
  let : ∀ r, IsScalarTower R S (U r) := fun r => baseTower R E (D r)
  let : ∀ r, IsScalarTower R T (U r) := fun r => baseTower R L (D r)
  let : ∀ r, IsLocalHom (algebraMap S (U r)) := fun r =>
    CompleteScalarBranch.oldRoot_isLocalHom R p r
  let : ∀ r, IsLocalHom (algebraMap T (U r)) := fun r =>
    CompleteScalarBranch.coefficient_isLocalHom R p r
  let : ∀ r, Module.Finite T (U r) := fun r => by
    let : Module.Finite R (U r) := integralClosure_finite_of_finite R F (D r)
    exact Module.Finite.of_restrictScalars_finite R T (U r)
  let : ∀ r, Module.IsTorsionFree T (U r) := fun r => upper_torsionFree R F L (D r)
  let : ∀ r, Algebra T (D r) := fun r =>
    AdjoinRoot.instAlgebra (S := T) (poly r.1.2)
  let : ∀ r, IsScalarTower T L (D r) := fun r =>
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ r, @IsScalarTower T (U r) (D r) _ _
      (AdjoinRoot.instSMulAdjoinRoot (S := T) (poly r.1.2)) := fun r => by
    let : Algebra T (D r) := AdjoinRoot.instAlgebra (S := T) (poly r.1.2)
    exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ r, IsIntegralClosure (U r) T (D r) := fun r =>
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
  have hRS := completeFinite_ramification_pair (algebraMap R S)
    (integralClosure_algebraMap_injective R F E) hπ hϖ
  have hRTpair := completeFinite_ramification_pair (algebraMap R T)
    (integralClosure_algebraMap_injective R F L) hπ hτ
  let eu : ℕ × Sˣ := hRS.choose
  let av : ℕ × Tˣ := hRTpair.choose
  have he : algebraMap R S π = (eu.2 : S) * ϖ ^ eu.1 := hRS.choose_spec
  have ha : algebraMap R T π = (av.2 : T) * τ ^ av.1 := hRTpair.choose_spec
  have hSU (r : I) := completeFinite_ramification_pair (algebraMap S (U r))
    (completeFinite_closureMap_injective R E (D r)) hϖ (hρ r)
  have hTU (r : I) := completeFinite_ramification_pair (algebraMap T (U r))
    (completeFinite_closureMap_injective R L (D r)) hτ (hρ r)
  let bw (r : I) : ℕ × (U r)ˣ := (hSU r).choose
  let cz (r : I) : ℕ × (U r)ˣ := (hTU r).choose
  have hb (r : I) : algebraMap S (U r) ϖ = ((bw r).2 : U r) * ρ r ^ (bw r).1 :=
    (hSU r).choose_spec
  have hc (r : I) : algebraMap T (U r) τ = ((cz r).2 : U r) * ρ r ^ (cz r).1 :=
    (hTU r).choose_spec
  have hRT (a : R) : algebraMap F L (algebraMap R F a) =
      algebraMap T L (algebraMap R T a) := by
    rw [← IsScalarTower.algebraMap_apply R F L, ← IsScalarTower.algebraMap_apply R T L]
  have hr := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (algebraMap R T) (algebraMap F L) hRT
      hπ hτ av.2 av.1 ha n) (milnorKNorm F E (n + 1) x)
  change dvrMilnorTameSymbol' T L n
      (milnorKTheoryMap (algebraMap F L) (n + 1) (milnorKNorm F E (n + 1) x)) =
    (av.1 : ℤ) • milnorKTheoryMap (ResidueField.map (algebraMap R T)) n
      (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x)) at hr
  simp only [natCast_zsmul] at hr
  let f (r : I) : E →+* D r :=
    AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2
  let branchNorm (r : I) : MilnorKTheory L (n + 1) :=
    milnorKNorm L (D r) (n + 1) (milnorKTheoryMap (f r) (n + 1) x)
  let resT : MilnorKTheory L (n + 1) →+ MilnorKTheory (ResidueField T) n :=
    dvrMilnorTameSymbol' T L n
  have hbase : milnorKTheoryMap (algebraMap F L) (n + 1) (milnorKNorm F E (n + 1) x) =
      ∑ r : I, branchNorm r := completeFinite_separable_norm_baseChange p hsep (n + 1) x
  let residueBranch (r : I) : MilnorKTheory (ResidueField T) n :=
    (bw r).1 • milnorKNorm (ResidueField T) (ResidueField (U r)) n
      (milnorKTransport (ResidueField.map (algebraMap S (U r))) n
        (dvrMilnorTameSymbol' S E n x))
  have hbranch (r : I) : resT (branchNorm r) = residueBranch r := by
    let y : MilnorKTheory (D r) (n + 1) := milnorKTheoryMap (f r) (n + 1) x
    have hnorm : resT (milnorKNorm L (D r) (n + 1) y) =
        milnorKNorm (ResidueField T) (ResidueField (U r)) n
          (dvrMilnorTameSymbol' (U r) (D r) n y) :=
      dvrMilnorTameSymbol'_milnorKNorm_complete_of_pGroup_finite
        T (U r) L (D r) Ω ℓ hG (g r) n y
    have hf (s : S) : f r (algebraMap S E s) =
        algebraMap (U r) (D r) (algebraMap S (U r) s) :=
      (CompleteScalarBranch.oldRoot_closureMap_apply R p r s).symm
    exact completeFinite_compare_branch S T (U r) E L (D r)
      (algebraMap S (U r)) (f r) hf hϖ (hρ r) (bw r).2 (bw r).1 (hb r) n x hnorm
  let residueSum : MilnorKTheory (ResidueField T) n := ∑ r : I, residueBranch r
  have hsum : av.1 • milnorKTheoryMap (ResidueField.map (algebraMap R T)) n
      (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x)) = residueSum := by
    calc
      _ = resT (milnorKTheoryMap (algebraMap F L) (n + 1) (milnorKNorm F E (n + 1) x)) := hr.symm
      _ = resT (∑ r : I, branchNorm r) := congrArg resT hbase
      _ = ∑ r : I, resT (branchNorm r) := map_sum resT branchNorm Finset.univ
      _ = _ := Finset.sum_congr rfl fun r _ => hbranch r
  have hcoordinates (r : I) (s : S) :
      algebraMap (U r) (D r) (algebraMap S (U r) s) =
        tensorScalarFactorsEquiv p hsep (1 ⊗ₜ[F] (algebraMap S E s)) r := by
    rw [tensorScalarFactorsEquiv_tmul_one]
    exact CompleteScalarBranch.oldRoot_closureMap_apply R p r s
  have hweighted : av.1 • milnorKTransport (algebraMap (ResidueField R) (ResidueField T)) n
      (milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x)) =
        residueSum :=
    milnorKNorm_residue_weighted_baseChange_of_finite
      R F S E T L D (fun r => ↥(U r)) (tensorScalarFactorsEquiv p hsep) hcoordinates hπ hϖ hτ
      eu.2 eu.1 he av.2 av.1 ha ρ hρ (fun r => (bw r).2) (fun r => (cz r).2)
      (fun r => (bw r).1) (fun r => (cz r).1) hb hc n (dvrMilnorTameSymbol' S E n x)
  exact completeFinite_defect_of_restriction R T F L hπ hτ av.2 av.1 ha n _ _ residueSum
    hsum hweighted

end SeparableRoot

private theorem completeFinite_of_separable_root
    (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) (hsep : (poly p).Separable)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    let _ := integralClosure_isDiscreteValuationRing_of_finite R F (AdjoinRoot (poly p))
    let _ := integralClosure_isLocalHom R F (AdjoinRoot (poly p))
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly p))
      (integralClosure R (AdjoinRoot (poly p)))
    let _ := integralClosure_residue_finite_of_finite R F (AdjoinRoot (poly p))
    dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField (integralClosure R (AdjoinRoot (poly p)))) n
        (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly p)))
          (AdjoinRoot (poly p)) n x) := by
  classical
  dsimp only
  apply sub_eq_zero.mp
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  by_contra h
  obtain ⟨ℓ, hℓ, hdiv⟩ := Nat.exists_prime_and_dvd h
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let Ω := (poly p).SplittingField
  let : IsGalois F Ω := IsGalois.of_separable_splitting_field hsep
  let P : Sylow ℓ (Ω ≃ₐ[F] Ω) := Classical.arbitrary _
  let L := IntermediateField.fixedField (P : Subgroup (Ω ≃ₐ[F] Ω))
  let : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)}) : AdjoinRoot (poly r.1.2) →ₐ[L] Ω :=
    Classical.choice (nonempty_algHom_branch_of_splits (L := L) (Ω := Ω)
      (poly p) (ne_zero p) (SplittingField.splits (poly p))
      (poly r.1.2) (irreducible r.1.2) r.2).1
  have hz := completeFinite_root_defect_annihilation p R hsep Ω ℓ
    (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ P) g n x
  exact (hℓ.coprime_iff_not_dvd.mp (IntermediateField.coprime_finrank_sylow_fixedField ℓ P))
    (hdiv.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz))

section Complete

variable (R F E S : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [FiniteDimensional F E]
  [Algebra R E] [IsScalarTower R F E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E]

private theorem completeFinite_of_separable [Algebra.IsSeparable F E]
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  obtain ⟨d, p, ⟨f⟩⟩ := exists_monicIrreducible_presentation F E
  have hsep : (poly p).Separable :=
    AdjoinRoot.polynomial_separable_of_algHom (poly p) (monic p) f.symm.toAlgHom
  let ε := f.symm
  let A := AdjoinRoot (poly p)
  let B := integralClosure R A
  let C := integralClosure R E
  have : FiniteDimensional F A := (AdjoinRoot.powerBasis' (monic p)).finite
  have : IsDiscreteValuationRing B := integralClosure_isDiscreteValuationRing_of_finite R F A
  have : IsLocalHom (algebraMap R B) := integralClosure_isLocalHom R F A
  have : IsFractionRing B A :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F A B
  have : Module.Finite (ResidueField R) (ResidueField B) :=
    integralClosure_residue_finite_of_finite R F A
  let j : B ≃ₐ[R] S := (ε.restrictScalars R).mapIntegralClosure.trans
    (IsIntegralClosure.equiv R C E S)
  have hj (b : B) : ε (algebraMap B A b) = algebraMap S E (j b) := by
    dsimp only [j, AlgEquiv.trans_apply]
    rw [IsIntegralClosure.algebraMap_equiv]
    rfl
  exact dvrMilnorTameSymbol'_milnorKNorm_of_algEquiv_of_finite j ε hj n
    (completeFinite_of_separable_root R F p hsep n) x

/-- The native norm commutes with the tame residue in the actual finite
DVR normalization of a complete DVR, in every characteristic. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete_of_finite
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  let J := separableClosure F E
  let : FiniteDimensional J E := FiniteDimensional.right F J E
  let : Algebra R J := ((algebraMap F J).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F J := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R J E := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply R F E, IsScalarTower.algebraMap_apply R F J,
      IsScalarTower.algebraMap_apply F J E]
  let T := integralClosure R J
  let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing_of_finite R F J
  let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F J
  let : Module.Finite R T := integralClosure_finite_of_finite R F J
  let : IsFractionRing T J := IsIntegralClosure.isFractionRing_of_finite_extension R F J T
  let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete_of_finite R F J
  let : Module.Finite (ResidueField R) (ResidueField T) :=
    integralClosure_residue_finite_of_finite R F J
  let : Algebra T S := IsIntegralClosure.IntermediateTower.closureAlgebra R S J E
  let : IsScalarTower R T S := IsIntegralClosure.IntermediateTower.baseTower R S J E
  let : IsScalarTower T S E := IsIntegralClosure.IntermediateTower.topTower R S J E
  let : IsIntegralClosure S T E :=
    IsIntegralClosure.IntermediateTower.upper_isIntegralClosure R S J E
  let : Module.Finite T S := IsIntegralClosure.IntermediateTower.upper_finite R S J E
  let : IsLocalHom (algebraMap T S) :=
    IsIntegralClosure.IntermediateTower.upper_isLocalHom R S J E
  exact dvrMilnorTameSymbol'_milnorKNorm_of_tower_of_finite R T S F J E n
    (completeFinite_of_separable R F J T n)
    (dvrMilnorTameSymbol'_milnorKNorm_complete_of_isPurelyInseparable_finite T S J E n) x

end Complete

end Stacks.Chow

end
