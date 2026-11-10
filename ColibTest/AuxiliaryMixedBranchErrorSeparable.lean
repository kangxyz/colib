/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.AuxiliaryMixedBranchErrorSeparable

open IsLocalRing Polynomial Stacks.Chow AdicCompletion
open Stacks.DiscreteValuationRing.Ramification
open scoped TensorProduct

noncomputable section

universe u

attribute [local irreducible] UniqueFactorizationMonoid.normalizedFactors
  UniqueFactorizationMonoid.factors

example
    (k R S F E K M : Type u)
    [Field k]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
    [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
    [FiniteDimensional F E] [IsGalois F E]
    [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    [FiniteDimensional F K] [IsDedekindDomain (integralClosure R K)]
    [Algebra k K] [IsScalarTower k R K]
    [Field M] [Algebra R M] [Algebra K M] [IsScalarTower R K M]
    [Algebra S M] [Algebra E M] [IsScalarTower S E M] [IsScalarTower R S M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (p : k[X]) (hmonic : p.Monic) (hsep : p.Separable)
    (econstant : AdjoinRoot (p.map (algebraMap k K)) ≃ₐ[K] M)
    (eta : K ⊗[F] E ≃ₐ[K] M)
    (heta : ∀ e : E, eta (1 ⊗ₜ[F] e) = algebraMap E M e)
    (hp : Nat.Prime (Module.finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K M) n) :
    let A : Type u := integralClosure R K
    let _ : CommRing A := inferInstance
    let _ : CommSemiring A := CommRing.toCommSemiring
    let _ : IsDedekindDomain A := inferInstance
    let _ : DecidableEq (Ideal A) := Classical.decEq _
    ∀ i : IdealBranch ((maximalIdeal R).map (algebraMap R A)),
    let T := BranchCompletion ((maximalIdeal R).map (algebraMap R A)) i
    let _ : IsLocalHom (algebraMap R T) := by
      rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime i.val) T]
      infer_instance
    (ramificationIdx R T : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 :=
  ramification_smul_restrict_norm_residue_difference_eq_zero_of_separable_constant_cover
    k R S F E K M p hmonic hsep econstant eta heta hp n x hmixed
