/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRResidueRamificationOneSeparable

/-! An actual homogeneous lower residue norm-square consumer in arbitrary characteristic. -/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module
open scoped TensorProduct BigOperators
open Stacks.Chow Stacks.DiscreteValuationRing.Ramification

universe u v w

namespace ColibTest.DVRResidueRamificationOneSeparable

variable (R S T : Type u) (F E L : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
  [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  [Module.IsTorsionFree R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field L]
  [Algebra R T] [FaithfulSMul R T] [IsLocalHom (algebraMap R T)] [Algebra T L]
  [IsFractionRing T L] [Algebra F L] [Algebra R L]
  [IsScalarTower R T L] [IsScalarTower R F L]
  {ι : Type w} [Fintype ι] (D : ι → Type v) (U : ι → Type u)
  [∀ i, Field (D i)] [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)]
  [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
  [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
  [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
  [∀ i, Module.IsTorsionFree T (U i)] [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Algebra R (U i)] [∀ i, Algebra S (U i)]
  [∀ i, FaithfulSMul S (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
  [Normal (ResidueField R) (ResidueField S)]

theorem actual_homogeneous_residue_square
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : S)
    (hc : ∀ i, algebraMap (U i) (D i) (algebraMap S (U i) b) =
      ε (1 ⊗ₜ[F] (algebraMap S E b)) i)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ ^ 1)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b)
    {τ : T} (hτ : Irreducible τ) (ω : ∀ i, U i)
    (hω : ∀ i, Irreducible (ω i)) (v : ∀ i, (U i)ˣ) (d : ι → ℕ)
    (hd : ∀ i, algebraMap T (U i) τ = (v i : U i) * ω i ^ d i)
    (hprime : Nat.Prime (finrank (ResidueField R) (ResidueField S)))
    (n : ℕ) (y : MilnorKTheory (ResidueField S) n) :
    (∑ i, (ramificationIdx S (U i) : ℤ) •
      milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
      (ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y) :=
  sum_ramification_smul_residue_norm_map_of_ramification_eq_one_of_separable_homogeneous
    R S T F E L D U ε b hc hπ hϖ u he B hB hτ ω hω v d hd hprime n y

end ColibTest.DVRResidueRamificationOneSeparable
