/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Charpoly.IntegralTensorProduct
public import Colib.RingTheory.Charpoly.DVRResidueArbitrary
public import Colib.RingTheory.Polynomial.PowerFactorCount
public import Mathlib.FieldTheory.Separable

/-!
# Separable residue-branch multiplicities

The actual generic tensor decomposition identifies the integral characteristic
polynomials. Reduction and unique factorization compute every residue-branch
multiplicity. Separability of the original residue extension supplies the squarefree
minimal polynomial; no characteristic restriction is imposed on either residue field.

The original tensor equivalence, integral lifts, residue power basis, uniformizer
equations and all ramification weights are retained. This extends the proof of
`Algebra.sum_residue_branch_degrees_eq_ramification` without assuming its conclusion.
The implementation is adapted from `Colib.RingTheory.Charpoly.DVRBranchCount`, whose
source provenance is retained there.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing
open scoped TensorProduct

namespace Algebra

variable (R F S E T L : Type*)
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
  {ι : Type*} [Fintype ι] (D U : ι → Type*)
  [∀ i, Field (D i)] [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)]
  [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
  [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
  [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
  [∀ i, Module.IsTorsionFree T (U i)] [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap T (U i))]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)] [DecidableEq (ResidueField T)]

/-- The full generic tensor decomposition forces the sum of ramification times
relative residue degree over each actual minimal-polynomial branch to be the
original ramification exponent. -/
theorem sum_residue_branch_degrees_eq_ramification_of_separable
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : S) (c : ∀ i, U i)
    (hc : ∀ i, algebraMap (U i) (D i) (c i) =
      ε (1 ⊗ₜ[F] (algebraMap S E b)) i)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b)
    {τ : T} (hτ : Irreducible τ) (ω : ∀ i, U i)
    (hω : ∀ i, Irreducible (ω i)) (v : ∀ i, (U i)ˣ) (d : ι → ℕ)
    (hd : ∀ i, algebraMap T (U i) τ = (v i : U i) * ω i ^ d i)
    (q : (ResidueField T)[X]) (hq : q.Monic) (hqirr : Irreducible q)
    (hqdvd : q ∣ (minpoly (ResidueField R) (residue S b)).map
      (algebraMap (ResidueField R) (ResidueField T))) :
    (∑ i, if minpoly (ResidueField T) (residue (U i) (c i)) = q then
      d i * Module.finrank
        (IntermediateField.adjoin (ResidueField T) {residue (U i) (c i)})
        (ResidueField (U i)) else 0) = e := by
  let P := (minpoly (ResidueField R) (residue S b)).map
    (algebraMap (ResidueField R) (ResidueField T))
  let p := fun i => minpoly (ResidueField T) (residue (U i) (c i))
  let w := fun i => d i * Module.finrank
    (IntermediateField.adjoin (ResidueField T) {residue (U i) (c i)})
    (ResidueField (U i))
  have hint := map_charpoly_lmul_eq_prod_integralClosure R F S E T L D U ε b c hc
  have hprod : P ^ e = ∏ i, p i ^ w i := calc
    P ^ e = ((lmul R S b).charpoly.map (residue R)).map
        (algebraMap (ResidueField R) (ResidueField T)) := by
      rw [residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis_arbitrary R S hπ hϖ u e he b B hB,
        Polynomial.map_pow]
    _ = ((lmul R S b).charpoly.map (algebraMap R T)).map (residue T) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    _ = (∏ i, (lmul T (U i) (c i)).charpoly).map (residue T) := by rw [hint]
    _ = ∏ i, p i ^ w i := by
      rw [Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact residue_charpoly_lmul_eq_minpoly_pow_arbitrary
        T (U i) hτ (hω i) (v i) (d i) (hd i) (c i)
  have hP : P.Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral (R := ResidueField R) (residue S b))).map _
  have hsep : (minpoly (ResidueField R) (residue S b)).Separable :=
    Algebra.IsSeparable.isSeparable (ResidueField R) (residue S b)
  have hPsq : Squarefree P := hsep.map.squarefree
  have hp : ∀ i, (p i).Monic ∧ Irreducible (p i) := fun i =>
    ⟨minpoly.monic (Algebra.IsIntegral.isIntegral (R := ResidueField T) (residue (U i) (c i))),
      minpoly.irreducible
        (Algebra.IsIntegral.isIntegral (R := ResidueField T) (residue (U i) (c i)))⟩
  exact Polynomial.sum_weights_eq_of_prod_eq_squarefree_pow
    P hP hPsq p hp w e hprod.symm q hq hqirr hqdvd

end Algebra
