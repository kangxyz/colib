/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletedBranchCoordinatesSeparable

open IsLocalRing Stacks.Chow AdicCompletion
open Stacks.DiscreteValuationRing.Ramification
open scoped TensorProduct

noncomputable section

universe u

attribute [local irreducible] UniqueFactorizationMonoid.normalizedFactors
  UniqueFactorizationMonoid.factors

-- The full actual completed branch family yields equality of both original transported norms.
example
    (R S F E B C K M : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
    [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
    [FiniteDimensional F E] [IsGalois F E]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra R B]
    [CommRing C] [IsDedekindDomain C] [Algebra B C] [Algebra S C]
    [Module.Finite B C] [Module.IsTorsionFree B C] [Algebra.Etale B C]
    [DecidableEq (Ideal C)]
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra F K]
    [Field M] [Algebra B M] [Algebra C M] [IsScalarTower B C M] [IsFractionRing C M]
    [Algebra K M] [IsScalarTower B K M] [Algebra E M]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    let J := (maximalIdeal B).map (algebraMap B C)
    let T := AdicCompletion (maximalIdeal B) B
    let L := FractionRing T
    let U := fun j : IdealBranch J => BranchCompletion J j
    -- Bind the original completion ring and its own semiring parent once.
    let uCommRing : ∀ j : IdealBranch J, CommRing (U j) := fun _j => inferInstance
    let _ : ∀ j : IdealBranch J, CommSemiring (U j) := fun j =>
      (uCommRing j).toCommSemiring
    let D := fun j : IdealBranch J => FractionRing (U j)
    -- Reuse the same fraction field and the exact abstract-field semiring path.
    let dField : ∀ j : IdealBranch J, Field (D j) := fun j => FractionRing.field (U j)
    let _ : ∀ j : IdealBranch J, CommRing (D j) := fun j => (dField j).toCommRing
    let _ : ∀ j : IdealBranch J, CommSemiring (D j) := fun j =>
      (dField j).toCommRing.toCommSemiring
    let _ : ∀ j : IdealBranch J, Semiring (D j) := fun j =>
      @CommSemiring.toSemiring (D j)
        (@Semifield.toCommSemiring (D j) (@Field.toSemifield (D j) (dField j)))
    let delta := fractionTensorEquivLocalFractionFields B C K M
    let _ : Algebra K L := fractionCompletionAlgebra B K
    let _ : SMul K L := Algebra.toSMul
    let _ : Module K L := Algebra.toModule
    let _ : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
    let _ : SMul F L := Algebra.toSMul
    let _ : Module F L := Algebra.toModule
    let _ : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
    let aTU : (j : IdealBranch J) → Algebra T (U j) := fun j =>
      localCompletionBaseAlgebra (R := B) (S := C) (maximalIdeal B) j
    let _ : (j : IdealBranch J) → SMul T (U j) := fun j => (aTU j).toSMul
    let _ : (j : IdealBranch J) → Module T (U j) := fun j =>
      @Algebra.toModule T (U j) _ _ (aTU j)
    let _ := fun j : IdealBranch J => localCompletionFractionAlgebra B C j
    let _ : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
    ∀ [FaithfulSMul R T] [IsLocalHom (algebraMap R T)]
      (epsilon : L ⊗[F] E ≃ₐ[L] ∀ j : IdealBranch J, D j)
      (_hRFL : IsScalarTower R F L)
      (_hright : ∀ (e : E) (j : IdealBranch J), epsilon (1 ⊗ₜ[F] e) j =
        delta.toFun ((1 : L) ⊗ₜ[K] algebraMap E M e) j)
      (_hintegral : ∀ (s : S) (j : IdealBranch J),
        epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
          algebraMap (U j) (D j) (algebraMap S (U j) s))
      (_htowers : ∀ j : IdealBranch J, IsScalarTower R S (U j) ∧
        IsScalarTower R T (U j) ∧ IsLocalHom (algebraMap S (U j)))
      (hinj : ∀ j : IdealBranch J, Function.Injective (algebraMap S (D j)))
      (_hfraction : ∀ j : IdealBranch J,
        (Pi.evalRingHom D j).comp
            (epsilon.toRingHom.comp
              (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E).toRingHom) =
          IsFractionRing.lift (K := E) (hinj j))
      (_hp : Nat.Prime (Module.finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)),
      milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
        milnorKMixedSpan (algebraMap K M) n →
      (ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x)) =
      (ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) := by
  classical
  intro J T L U _ _ D _ _ _ _ delta _ _ _ _ _ _ _ aTU _ _ aLD _
    _ _ epsilon hRFL hright hintegral htowers hinj hfraction hp n x hmixed
  have h :=
    ramification_smul_restrict_norm_residue_difference_eq_zero_of_etale_completed_coordinates
      R S F E B C K M epsilon hRFL hright hintegral htowers hinj hfraction hp n x hmixed
  rw [map_sub, smul_sub] at h
  exact sub_eq_zero.mp h
