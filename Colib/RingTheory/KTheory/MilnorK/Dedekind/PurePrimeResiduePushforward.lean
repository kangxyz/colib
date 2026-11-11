/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeOriginal
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeResidueEquiv
public import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResidueSupport
public import Colib.RingTheory.Localization.FiniteResidue
public import Colib.RingTheory.Localization.DedekindFractions

import Colib.RingTheory.KTheory.MilnorK.Residue.Automorphism

/-!
# Purely inseparable prime norm and residue at a Dedekind prime

The actual finite model localized at the lower prime computes the norm.
The native localization equivalence preserves the original fraction-field
map and therefore identifies the branch residue and its residue norm.
-/

@[expose] public noncomputable section

open IsLocalRing IsDedekindDomain Module AdicCompletion

universe u

namespace Stacks.Chow

attribute [local instance] Classical.decEq

variable (A S F E : Type u)
  [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [Field F] [Algebra A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [IsPurelyInseparable F E]
  (p : HeightOneSpectrum A)
  [Algebra (Localization.AtPrime p.asIdeal) F] [IsFractionRing (Localization.AtPrime p.asIdeal) F]
  [IsScalarTower A (Localization.AtPrime p.asIdeal) F]
  (q : IdealBranch (p.asIdeal.map (algebraMap A S)))
  [Algebra (Localization.AtPrime q.val) E] [IsFractionRing (Localization.AtPrime q.val) E]
  [IsScalarTower S (Localization.AtPrime q.val) E]

local notation "R" => Localization.AtPrime p.asIdeal
local notation "U" => Localization.AtPrime q.val
local notation "under" => Localization.originalIdealBranch_under p q

/-- At the original upper prime, the residue field is purely inseparable of
degree dividing the prime field degree, and its native norm computes the
residue of the original generic norm. -/
theorem purePrimeResidue_atPrime (hp : Nat.Prime (finrank F E)) :
    letI := Localization.basePrimeLocalAlgebra p.asIdeal q.val under
    letI := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val under
    letI := Localization.basePrimeLocal_residueFinite p.asIdeal q.val under
    IsPurelyInseparable (ResidueField R) (ResidueField U) ∧
      finrank (ResidueField R) (ResidueField U) ∣ finrank F E ∧
      ∀ (n : ℕ) (x : MilnorKTheory E (n + 1)),
        dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
          milnorKNorm (ResidueField R) (ResidueField U) n (dvrMilnorTameSymbol' U E n x) := by
  classical
  let B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A R E := IsScalarTower.to₁₂₄ A R F E
  let := Localization.baseLocalizedFractionAlgebra (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionTower (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionRing (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionBaseTower (S := S) p.asIdeal E
  let Q := Localization.originalIdealBranchEquivLocalizedBranches (S := S) p q
  let T := Localization.AtPrime Q.val
  let := originalBranchFractionAlgebra B E Q
  let := originalBranchIsFractionRing B E Q
  let := originalBranchFractionTower B E Q
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val under
  let := Localization.basePrimeLocalTower p.asIdeal q.val under
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val under
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val under
  let jR := Localization.originalIdealBranchLocalEquiv (S := S) p q
  let τ := ResidueField.mapAlgEquiv' jR
  let σ := RingEquiv.refl (ResidueField R)
  have hστ : τ.toRingEquiv.toRingHom.comp (algebraMap (ResidueField R) (ResidueField T)) =
      (algebraMap (ResidueField R) (ResidueField U)).comp σ.toRingHom :=
    RingHom.ext fun a ↦ τ.commutes a
  obtain ⟨hPure, hDiv⟩ := originalBranch_residue_isPurelyInseparable_and_finrank_dvd R B F E Q
  let : IsPurelyInseparable (ResidueField R) (ResidueField T) := hPure
  refine ⟨IsPurelyInseparable.of_equiv_equiv σ τ.toRingEquiv hστ, ?_, ?_⟩
  · rw [← Algebra.finrank_eq_of_equiv_equiv σ τ.toRingEquiv hστ.symm]
    exact hDiv
  · intro n x
    have hSquare :=
      dvrMilnorTameSymbol'_milnorKNorm_eq_originalBranch_of_isPurelyInseparable_of_prime
        R B F E Q hp n x
    let : IsScalarTower S T E := IsScalarTower.to₁₃₄ S B T E
    have hj (b : T) : algebraMap T E b = algebraMap U E (jR b) := by
      have h := Localization.atPrime_basePrimeCompl_equiv_comp p.asIdeal q.val under
        (IsScalarTower.toAlgHom S T E) (IsScalarTower.toAlgHom S U E)
      exact (AlgHom.congr_fun h b).symm
    have hτ : ResidueField.map (jR.toRingEquiv : T →+* U) = τ.toRingEquiv.toRingHom := rfl
    have hResidue : dvrMilnorTameSymbol' U E n x =
        milnorKTransport τ.toRingEquiv.toRingHom n (dvrMilnorTameSymbol' T E n x) := by
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap,
        milnorKTransport_id_apply, hτ] using
        DFunLike.congr_fun (dvrMilnorTameSymbol'_map_ringEquiv jR.toRingEquiv
          (RingHom.id E) hj n) x
    have hNorm := milnorKNorm_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime
      hp hDiv σ τ.toRingEquiv hστ n (dvrMilnorTameSymbol' T E n x)
    simp only [σ, RingEquiv.toRingHom_refl', milnorKTransport_id_apply] at hNorm
    exact hSquare.trans (hNorm.trans
      (congrArg (milnorKNorm (ResidueField R) (ResidueField U) n) hResidue.symm))

/-- The native norm–residue square at the original upper prime of a purely
inseparable prime-degree finite Dedekind extension. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_atPrime_of_isPurelyInseparable_of_prime
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    letI := Localization.basePrimeLocalAlgebra p.asIdeal q.val under
    letI := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val under
    letI := Localization.basePrimeLocal_residueFinite p.asIdeal q.val under
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField U) n (dvrMilnorTameSymbol' U E n x) :=
  (purePrimeResidue_atPrime A S F E p q hp).2.2 n x

end Stacks.Chow

end
