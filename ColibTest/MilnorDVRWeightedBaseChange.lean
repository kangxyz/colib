/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRWeightedBaseChange

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing

universe u v

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

open scoped TensorProduct

variable (R F S E T L : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
  [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  [Module.IsTorsionFree R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field L]
  [Algebra R T] [IsLocalHom (algebraMap R T)] [Algebra T L]
  [IsFractionRing T L] [Algebra F L] [Algebra R L]
  [IsScalarTower R T L] [IsScalarTower R F L]
  {ι : Type u} [Fintype ι] (D U : ι → Type u)
  [∀ i, Field (D i)] [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)]
  [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
  [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
  [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
  [∀ i, IsFractionRing (U i) (D i)]
  [∀ i, Module.IsTorsionFree T (U i)] [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Algebra S (U i)] [∀ i, Algebra R (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))] [∀ i, IsLocalHom (algebraMap R (U i))]
  [CharZero (ResidueField R)] [CharZero (ResidueField T)]

example
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (θ : S)
    (hθ : ∀ i, algebraMap (U i) (D i) (algebraMap S (U i) θ) =
      ε (1 ⊗ₜ[F] (algebraMap S E θ)) i)
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = IsLocalRing.residue S θ)
    (ρ : ∀ i, U i) (hρ : ∀ i, Irreducible (ρ i))
    (w z : ∀ i, (U i)ˣ) (b c : ι → ℕ)
    (hb : ∀ i, algebraMap S (U i) ϖ = (w i : U i) * ρ i ^ b i)
    (hc : ∀ i, algebraMap T (U i) τ = (z i : U i) * ρ i ^ c i)
    (n : ℕ) (x : MilnorKTheory (ResidueField S) n) :
    a • milnorKTransport (algebraMap (ResidueField R) (ResidueField T)) n
      (milnorKNorm (ResidueField R) (ResidueField S) n x) =
      ∑ i, b i • milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (milnorKTransport (ResidueField.map (algebraMap S (U i))) n x) :=
  milnorKNorm_residue_weighted_baseChange R F S E T L D U ε θ hθ
    hπ hϖ hτ u e he v a ha B hB ρ hρ w z b c hb hc n x

end
