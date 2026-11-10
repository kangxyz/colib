/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRBranchWeightedError
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRBranchWeightedErrorSeparable

/-! Actual simultaneous-import consumer of the separable weighted error identity. -/

@[expose] public noncomputable section

open IsLocalRing Module
open scoped TensorProduct BigOperators

universe u v w

namespace Stacks.Chow

open DiscreteValuationRing.Ramification

variable (R S T : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Algebra R T] [FaithfulSMul R T] [IsLocalHom (algebraMap R T)]
  (F E K : Type v)
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
  [FiniteDimensional F E] [IsGalois F E]
  [Field K] [Algebra T K] [IsFractionRing T K] [Algebra F K]
  [Algebra R K] [IsScalarTower R T K] [IsScalarTower R F K]
  {ι : Type w} [Finite ι] (U : ι → Type u) (D : ι → Type v)
  [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)] [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra R (U i)] [∀ i, Algebra S (U i)] [∀ i, Algebra T (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, FaithfulSMul S (U i)] [∀ i, Module.IsTorsionFree T (U i)]
  [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))] [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Field (D i)] [∀ i, Algebra (U i) (D i)] [∀ i, IsFractionRing (U i) (D i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra K (D i)]
  [∀ i, IsScalarTower T (U i) (D i)] [∀ i, IsScalarTower T K (D i)]
  [∀ i, FiniteDimensional K (D i)]
  [∀ i, Algebra E (D i)] [∀ i, Algebra S (D i)]
  [∀ i, IsScalarTower S E (D i)] [∀ i, IsScalarTower S (U i) (D i)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]


include U in
theorem actual_unramified_weighted_error_consumer
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hcoordinate : ∀ (e : E) (i : ι), ε (1 ⊗ₜ[F] e) i = algebraMap E (D i) e)
    (hbranchone : ∀ i, ramificationIdx T (U i) = 1)
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : ∀ i, milnorKTheoryMap (algebraMap E (D i)) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K (D i)) n) :
    (ramificationIdx R T : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  exact ramification_smul_restrict_norm_residue_difference_eq_zero_of_unramified_mixed_branches
    R S T F E K U D ε hcoordinate hbranchone hp n x hmixed

end Stacks.Chow

end
