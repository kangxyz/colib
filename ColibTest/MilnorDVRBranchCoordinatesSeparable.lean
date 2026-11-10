/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRBranchCoordinatesSeparable

open IsLocalRing Stacks.Chow
open Stacks.DiscreteValuationRing.Ramification
open scoped TensorProduct

noncomputable section

universe u

-- The actual native DVR/tensor/fraction coordinates imply equality of both transported terms.
-- No E/D action, source scalar tower or branchwise mixed membership is assumed here.
example
    (R S T F E L K M : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Algebra R T] [FaithfulSMul R T] [IsLocalHom (algebraMap R T)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
    [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
    [FiniteDimensional F E] [IsGalois F E]
    [Field L] [Algebra T L] [IsFractionRing T L] [Algebra F L]
    [Algebra R L] [IsScalarTower R T L] [IsScalarTower R F L]
    [Field K] [Field M] [Algebra K M] [Algebra K L] [Algebra E M]
    {ι : Type u} [Finite ι] (U D : ι → Type u)
    [∀ j, CommRing (U j)] [∀ j, IsDomain (U j)] [∀ j, IsDiscreteValuationRing (U j)]
    [∀ j, Algebra R (U j)] [∀ j, Algebra S (U j)] [∀ j, Algebra T (U j)]
    [∀ j, IsScalarTower R S (U j)] [∀ j, IsScalarTower R T (U j)]
    [∀ j, Module.IsTorsionFree T (U j)] [∀ j, Module.Finite T (U j)]
    [∀ j, IsLocalHom (algebraMap S (U j))] [∀ j, IsLocalHom (algebraMap T (U j))]
    [∀ j, Field (D j)] [∀ j, Algebra (U j) (D j)] [∀ j, IsFractionRing (U j) (D j)]
    [∀ j, Algebra T (D j)] [∀ j, Algebra L (D j)] [∀ j, Algebra S (D j)]
    [∀ j, IsScalarTower T (U j) (D j)] [∀ j, IsScalarTower T L (D j)]
    [∀ j, IsScalarTower S (U j) (D j)] [∀ j, FiniteDimensional L (D j)]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (epsilon : L ⊗[F] E ≃ₐ[L] ∀ j, D j)
    (delta : L ⊗[K] M ≃ₐ[L] ∀ j, D j)
    (hinj : ∀ j, Function.Injective (algebraMap S (D j)))
    (hfraction : ∀ j,
      (Pi.evalRingHom D j).comp
          (epsilon.toRingHom.comp
            (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E).toRingHom) =
        IsFractionRing.lift (K := E) (hinj j))
    (hright : ∀ (e : E) (j : ι), epsilon (1 ⊗ₜ[F] e) j =
      delta.toFun ((1 : L) ⊗ₜ[K] algebraMap E M e) j)
    (hintegral : ∀ (s : S) (j : ι),
      epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
        algebraMap (U j) (D j) (algebraMap S (U j) s))
    (hbranchone : ∀ j, ramificationIdx T (U j) = 1)
    (hp : Nat.Prime (Module.finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K M) n) :
    (ramificationIdx R T : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x)) =
    (ramificationIdx R T : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
        (milnorKNorm (ResidueField R) (ResidueField S) n
          (dvrMilnorTameSymbol' S E n x)) := by
  have h :=
    ramification_smul_restrict_norm_residue_difference_eq_zero_of_auxiliary_coordinates
      R S T F E L K M U D epsilon delta hinj hfraction hright hintegral hbranchone hp n x hmixed
  rw [map_sub, smul_sub] at h
  exact sub_eq_zero.mp h
