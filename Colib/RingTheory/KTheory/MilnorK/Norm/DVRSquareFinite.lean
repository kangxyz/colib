/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparisonFinite
public import Colib.RingTheory.KTheory.MilnorK.Residue.Automorphism
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Towers and transport of DVR norm-residue squares

Compatible equivalences and actual finite towers transport and compose the
native norm-residue identities in arbitrary characteristic. The degree-one
square is the transport of the identity square along the original fraction
and integral closure maps.

The proofs generalize the Colib adaptations from Aglib's
`DVRResidueTower.lean`, `DVRResidueEquiv.lean` and `CompleteDegreeOne.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

universe u v

/-- Two actual local norm-residue squares compose in their original scalar towers. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_tower_of_finite
    (R S T : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    [IsLocalHom (algebraMap R T)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField S) (ResidueField T)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    (F E L : Type u) [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
    [Algebra T L] [IsFractionRing T L]
    (n : ℕ)
    (lower : ∀ y : MilnorKTheory E (n + 1),
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) y) =
        milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n y))
    (upper : ∀ z : MilnorKTheory L (n + 1),
      dvrMilnorTameSymbol' S E n (milnorKNorm E L (n + 1) z) =
        milnorKNorm (ResidueField S) (ResidueField T) n (dvrMilnorTameSymbol' T L n z))
    (x : MilnorKTheory L (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F L (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField T) n (dvrMilnorTameSymbol' T L n x) := by
  calc
    _ = dvrMilnorTameSymbol' R F n
        (milnorKNorm F E (n + 1) (milnorKNorm E L (n + 1) x)) := by
      rw [milnorKNorm_tower_of_finite]
    _ = milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n (milnorKNorm E L (n + 1) x)) := lower _
    _ = milnorKNorm (ResidueField R) (ResidueField S) n
        (milnorKNorm (ResidueField S) (ResidueField T) n (dvrMilnorTameSymbol' T L n x)) := by
      rw [upper]
    _ = _ := milnorKNorm_tower_of_finite n _

/-- Actual compatible algebra equivalences transport a proved local norm-residue square. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_algEquiv_of_finite
    {R S T : Type v} {F E L : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [FiniteDimensional F E] [FiniteDimensional F L]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E] [Algebra T L] [IsFractionRing T L]
    (j : S ≃ₐ[R] T) (ε : E ≃ₐ[F] L)
    (hε : ∀ s : S, ε (algebraMap S E s) = algebraMap T L (j s))
    (n : ℕ)
    (hsource : ∀ y : MilnorKTheory E (n + 1),
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) y) =
        milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n y))
    (x : MilnorKTheory L (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F L (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField T) n (dvrMilnorTameSymbol' T L n x) := by
  have hex : ∃ y : MilnorKTheory E (n + 1), milnorKTheoryMap ε.toRingHom (n + 1) y = x := by
    refine ⟨milnorKTheoryMap ε.symm.toRingHom (n + 1) x, ?_⟩
    rw [← LinearMap.comp_apply, ← milnorKTheoryMap_comp]
    have hi : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id L := by
      ext a
      exact ε.apply_symm_apply a
    rw [hi, milnorKTheoryMap_id, LinearMap.id_apply]
  obtain ⟨y, rfl⟩ := hex
  have hres := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ringEquiv j.toRingEquiv ε.toRingHom hε n) y
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hres
  rw [milnorKNorm_map_algEquiv_of_finite ε, hsource, hres]
  exact (milnorKNorm_map_algEquiv_of_finite (ResidueField.mapAlgEquiv' j) n _).symm

/-- A degree-one field extension satisfies the native residue square in every degree. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_finrank_eq_one_of_finite
    (R S : Type v) (F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra R E] [IsScalarTower R F E]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    (hd : Module.finrank F E = 1) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  let ε : F ≃ₐ[F] E := AlgEquiv.ofBijective (Algebra.ofId F E)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd)
  let j₀ : R ≃ₐ[R] integralClosure R F := IsIntegralClosure.equiv R R F _
  let j₁ : integralClosure R F ≃ₐ[R] integralClosure R E :=
    (ε.restrictScalars R).mapIntegralClosure
  let j₂ : integralClosure R E ≃ₐ[R] S := IsIntegralClosure.equiv R _ E S
  let j : R ≃ₐ[R] S := (j₀.trans j₁).trans j₂
  have hj (r : R) : ε (algebraMap R F r) = algebraMap S E (j r) := by
    dsimp only [j, AlgEquiv.trans_apply, j₂]
    rw [IsIntegralClosure.algebraMap_equiv]
    change ε (algebraMap R F r) = ε (algebraMap (integralClosure R F) F (j₀ r))
    rw [IsIntegralClosure.algebraMap_equiv]
  apply dvrMilnorTameSymbol'_milnorKNorm_of_algEquiv_of_finite j ε hj n (fun y => ?_) x
  have hself : milnorKNorm F F (n + 1) y = y := by
    apply Subtype.ext
    rw [coe_milnorKNorm]
    have h := milnorKNormRing_milnorKRingMap (K := F) (L := F) (y : MilnorKRing F)
    change milnorKNormRing F F (milnorKRingMap (RingHom.id F) (y : MilnorKRing F)) =
      (Module.finrank F F : ℤ) • (y : MilnorKRing F) at h
    simpa only [milnorKRingMap_id_apply, Module.finrank_self, Nat.cast_one, one_smul] using h
  rw [hself]
  let : Algebra (ResidueField R) (ResidueField R) := ResidueField.instAlgebra
  have hid : algebraMap (ResidueField R) (ResidueField R) = RingHom.id _ := by
    ext a
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    rfl
  have hbij : Function.Bijective (algebraMap (ResidueField R) (ResidueField R)) := by
    rw [hid]
    exact Function.bijective_id
  have hdegree := Module.finrank_of_bijective_algebraMap hbij
  apply Subtype.ext
  rw [coe_milnorKNorm]
  have h := milnorKNormRing_milnorKRingMap (K := ResidueField R) (L := ResidueField R)
    (dvrMilnorTameSymbol' R F n y : MilnorKRing (ResidueField R))
  rw [hid, milnorKRingMap_id_apply, hdegree, Nat.cast_one, one_smul] at h
  exact h.symm

end Stacks.Chow

end
