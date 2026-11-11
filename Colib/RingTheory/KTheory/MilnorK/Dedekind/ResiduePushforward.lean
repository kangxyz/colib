/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVR
public import Colib.RingTheory.KTheory.MilnorK.Residue.Automorphism
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparisonFinite
public import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResidueSupport
public import Colib.RingTheory.Localization.FiniteResidue
public import Colib.RingTheory.Localization.DedekindFractions

/-!
# Original-point residue pushforward for a finite Dedekind map

The local comparison uses the actual localized rings and their maps to the
same original fraction field. No residue compatibility premise is introduced.

Adapted from `Aglib/KTheory/MilnorK/Dedekind/ResiduePushforward.lean`,
revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 25–129.
The original prime indices and localization-to-original-field triangles are
retained. Finite norm equivariance and the original-branch DVR formula extend
the source's characteristic-zero comparison to arbitrary fields in a common
universe.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

universe u

/-- Equivalent actual local models compute the same residue norm in the
original base residue field. -/
theorem residueNorm_eq_of_localAlgEquiv
    {R S T E : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    [Field E] [Algebra S E] [IsFractionRing S E] [Algebra T E] [IsFractionRing T E]
    (j : S ≃ₐ[R] T)
    (hj : ∀ s : S, algebraMap S E s = algebraMap T E (j s))
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) =
      milnorKNorm (ResidueField R) (ResidueField T) n (dvrMilnorTameSymbol' T E n x) := by
  have hr : dvrMilnorTameSymbol' T E n x =
      milnorKTheoryMap (ResidueField.map (j.toRingEquiv : S →+* T)) n
        (dvrMilnorTameSymbol' S E n x) := by
    simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      milnorKTheoryMap_id, LinearMap.id_apply] using
      DFunLike.congr_fun
        (dvrMilnorTameSymbol'_map_ringEquiv j.toRingEquiv (RingHom.id E) hj n) x
  rw [hr]
  exact (milnorKNorm_map_algEquiv_of_finite (ResidueField.mapAlgEquiv' j) n _).symm

open _root_.AdicCompletion IsDedekindDomain
attribute [local instance] Classical.decEq

section Dedekind
variable (A S F E : Type u) [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]
  (p : HeightOneSpectrum A)

omit F in
/-- The actual norm of the original residue at one original prime above `p`. -/
def originalBranchResidueNorm (n : ℕ) (x : MilnorKTheory E (n + 1))
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    MilnorKTheory (ResidueField (Localization.AtPrime p.asIdeal)) n := by
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := originalBranchFractionAlgebra S E q
  let := originalBranchIsFractionRing S E q
  exact milnorKNorm (ResidueField (Localization.AtPrime p.asIdeal))
    (ResidueField (Localization.AtPrime q.val)) n
      (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n x)

/-- The finite norm-residue square at an original height-one point, summing
all original prime ideals above it. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_atPrime (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' (Localization.AtPrime p.asIdeal) F n
      (milnorKNorm F E (n + 1) x) =
      ∑ q : IdealBranch (p.asIdeal.map (algebraMap A S)),
        originalBranchResidueNorm A S E p n x q := by
  classical
  let R := Localization.AtPrime p.asIdeal
  let B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A R E := IsScalarTower.to₁₂₄ A R F E
  let := Localization.baseLocalizedFractionAlgebra (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionTower (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionRing (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionBaseTower (S := S) p.asIdeal E
  let J := (maximalIdeal R).map (algebraMap R B)
  let := fun q : IdealBranch J => originalBranchFractionAlgebra B E q
  let := fun q : IdealBranch J => originalBranchIsFractionRing B E q
  let := fun q : IdealBranch J => originalBranchFractionTower B E q
  rw [dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches R B F E]
  let e := Localization.originalIdealBranchEquivLocalizedBranches (S := S) p
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  let Q := e q
  let := originalBranchFractionAlgebra S E q
  let := originalBranchIsFractionRing S E q
  let := originalBranchFractionTower S E q
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocalTower p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let jR := Localization.originalIdealBranchLocalEquiv (S := S) p q
  apply residueNorm_eq_of_localAlgEquiv jR
  intro b
  have ht : IsScalarTower S (Localization.AtPrime Q.val) E :=
    IsScalarTower.to₁₃₄ S B (Localization.AtPrime Q.val) E
  let := ht
  have hh := Localization.atPrime_basePrimeCompl_equiv_comp p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
    (IsScalarTower.toAlgHom S (Localization.AtPrime Q.val) E)
    (IsScalarTower.toAlgHom S (Localization.AtPrime q.val) E)
  exact (AlgHom.congr_fun hh b).symm

end Dedekind

end Stacks.Chow

attribute [colib_tag "COL-1002",
  colib_ref "aglib_milnor_4f65be4e"
    "KTheory/MilnorK/Dedekind/ResiduePushforward.lean:83-129" "adaptation"
    "The local norm–residue identity at an original point in arbitrary characteristic"]
  Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_atPrime
