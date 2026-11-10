/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRResiduePrimeBranchesSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeTensorBaseChangeSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixed

/-!
# Weighted error over the actual unramified mixed branches

The original generic and residue norm formulas are derived over every field of
constants using separability of the original residue extension. Actual branch
ramification index one supplies the mixed norm-residue square in arbitrary
characteristic. No norm-square premise, auxiliary separability, Henselianity,
invertibility of the prime or cancellation of a ramification index is assumed.

All original fields, tensor coordinates, residue maps and ramification weights
are retained. The branch index-one premise is structural and must be supplied
by finite étale geometry for the eventual constant Laurent cover application.
This lower error identity alone is not the all-symbol Laurent square.
-/

@[expose] public noncomputable section

open IsLocalRing Module
open scoped TensorProduct BigOperators

universe u v w

namespace Stacks.Chow

open DiscreteValuationRing.Ramification

private theorem canonical_residue_map_eq_ramification_smul
    (R S : Type u) (F E : Type v)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
    (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' S E n (milnorKTheoryMap (algebraMap F E) (n + 1) x) =
      (ramificationIdx R S : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
          (dvrMilnorTameSymbol' R F n x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero) hρ
  have hidx : e = ramificationIdx R S := by
    have h := addVal_algebraMap_eq_ramificationIdx R S π hπ
    rw [he, IsDiscreteValuationRing.addVal_def' u hρ e] at h
    exact_mod_cast h
  have hf : ∀ r : R, algebraMap F E (algebraMap R F r) =
      algebraMap S E (algebraMap R S r) := fun r =>
    (IsScalarTower.algebraMap_apply R F E r).symm.trans
      (IsScalarTower.algebraMap_apply R S E r)
  have h := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (algebraMap R S) (algebraMap F E) hf
      hπ hρ u e he n) x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, hidx] at h
  exact h

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
/-- If the original class is mixed in every actual tensor factor, the actual base-change
ramification index kills the restriction of its original norm-residue error. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero_of_unramified_mixed_branches
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
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let pb := Field.powerBasisOfFiniteOfSeparable F E
  have hmap (i : ι) : (Pi.evalRingHom D i).comp
      (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) =
        algebraMap E (D i) := RingHom.ext fun e => hcoordinate e i
  have hupper := milnorKNorm_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable
    pb ε hp (n + 1) x
  simp only [hmap] at hupper
  have hbranch (i : ι) :
      dvrMilnorTameSymbol' T K n
        (milnorKNorm K (D i) (n + 1)
          (milnorKTheoryMap (algebraMap E (D i)) (n + 1) x)) =
      milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (dvrMilnorTameSymbol' (U i) (D i) n
          (milnorKTheoryMap (algebraMap E (D i)) (n + 1) x)) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (U i)
    obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective T (U i))).mpr hπ.ne_zero) hϖ
    have heone : e = 1 := by
      have h := addVal_algebraMap_eq_ramificationIdx T (U i) π hπ
      rw [he, IsDiscreteValuationRing.addVal_def' u hϖ e, hbranchone i] at h
      exact_mod_cast h
    subst e
    exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exponent_one
      T (U i) K (D i) hπ hϖ u (by simpa only [pow_one] using he) n _ (hmixed i)
  have hR := canonical_residue_map_eq_ramification_smul R T F K n
    (milnorKNorm F E (n + 1) x)
  have hS (i : ι) := canonical_residue_map_eq_ramification_smul
    S (U i) E (D i) n x
  have hintegral (s : S) (i : ι) :
      algebraMap (U i) (D i) (algebraMap S (U i) s) =
        ε (1 ⊗ₜ[F] algebraMap S E s) i := by
    rw [hcoordinate]
    exact (IsScalarTower.algebraMap_apply S (U i) (D i) s).symm.trans
      (IsScalarTower.algebraMap_apply S E (D i) s)
  rw [map_sub, smul_sub]
  apply sub_eq_zero.mpr
  rw [← hR, hupper, map_sum]
  simp_rw [hbranch, hS, map_zsmul]
  exact sum_ramification_smul_residue_norm_map_of_prime_galois_of_separable_homogeneous
    R S T F E K U D ε hintegral hp n (dvrMilnorTameSymbol' S E n x)

end Stacks.Chow

end
