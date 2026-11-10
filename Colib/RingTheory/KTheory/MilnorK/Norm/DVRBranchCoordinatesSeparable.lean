/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRBranchWeightedErrorSeparable
public import Colib.RingTheory.KTheory.MilnorK.Symbols.MixedMap

/-!
# Weighted norm-residue error from original branch coordinates

This structural interface uses native DVRs, their fraction fields, two original tensor
coordinate equivalences and the original source fraction lift. An auxiliary mixed witness
is transported to all supplied unramified branches before applying the chosen weighted
norm-residue identity. The source action and its scalar towers are constructed over abstract
carriers, so later normalization applications can reuse the checked proof.

No normalization, finite-etale cover, characteristic-zero hypothesis, auxiliary separability,
replacement norm or norm-square hypothesis is introduced here. Actual branch index one is
an input to this lower interface and must be proved in its geometric applications.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.Chow

open DiscreteValuationRing.Ramification

private theorem mem_mixedSpan_of_tensor_coordinates
    (K M L E : Type u) [Field K] [Field M] [Field L] [Field E]
    [Algebra K M] [Algebra K L] [Algebra E M]
    {ι : Type u} (D : ι → Type u) [∀ j, Field (D j)]
    [∀ j, Algebra L (D j)] [∀ j, Algebra E (D j)]
    (delta : L ⊗[K] M ≃ₐ[L] ∀ j, D j)
    (hsource : ∀ (e : E) (j : ι),
      delta.toFun ((1 : L) ⊗ₜ[K] algebraMap E M e) j = algebraMap E (D j) e)
    (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K M) n) :
    ∀ j, milnorKTheoryMap (algebraMap E (D j)) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L (D j)) n := by
  have hbase (k : K) (j : ι) :
      delta.toFun ((1 : L) ⊗ₜ[K] algebraMap K M k) j =
        algebraMap L (D j) (algebraMap K L k) := by
    have h : (1 : L) ⊗ₜ[K] algebraMap K M k =
        algebraMap L (L ⊗[K] M) (algebraMap K L k) := by
      rw [← Algebra.TensorProduct.algebraMap_apply',
        IsScalarTower.algebraMap_apply K L (L ⊗[K] M)]
    rw [h]
    exact congrFun (delta.commutes (algebraMap K L k)) j
  intro j
  let rho : M →+* D j := (Pi.evalAlgHom L D j).toRingHom.comp
    (delta.toRingHom.comp
      (Algebra.TensorProduct.includeRight : M →ₐ[K] L ⊗[K] M).toRingHom)
  have hsquare : rho.comp (algebraMap K M) =
      (algebraMap L (D j)).comp (algebraMap K L) := by
    ext k
    exact hbase k j
  have hmap : rho.comp (algebraMap E M) = algebraMap E (D j) := by
    ext e
    exact hsource e j
  have h := milnorKTheoryMap_mem_mixedSpan_of_comm (algebraMap K M)
    (algebraMap K L) rho (algebraMap L (D j)) hsquare n
    (milnorKTheoryMap (algebraMap E M) (n + 1) x) hmixed
  have hcomp : milnorKTheoryMap (rho.comp (algebraMap E M)) (n + 1) x =
      milnorKTheoryMap rho (n + 1)
        (milnorKTheoryMap (algebraMap E M) (n + 1) x) := by
    rw [milnorKTheoryMap_comp, LinearMap.comp_apply]
  rw [← hcomp, hmap] at h
  exact h

/-- Original tensor and fraction coordinates transport one auxiliary mixed witness to
all unramified DVR branches. Their native ramification weight then kills the restriction
of the original chosen norm-residue difference.

The source fraction action is constructed from the given tensor coordinate and proved equal
to the original fraction lift. Its scalar towers and branchwise mixed memberships are derived
inside the proof. The inputs are structural coordinate equations, actual branch index one,
and the original mixed witness; no norm-compatibility premise or auxiliary separability is used.
This interface does not construct normalizations or prove that a supplied branch is unramified. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero_of_auxiliary_coordinates
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
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  let gED : ∀ j : ι, E →+* D j := fun j =>
    (Pi.evalRingHom D j).comp
      (epsilon.toRingHom.comp
        (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E).toRingHom)
  have hcoordinate_eq_original_fraction_lift (j : ι) :
      gED j = IsFractionRing.lift (K := E) (hinj j) := hfraction j
  let aED : ∀ j : ι, Algebra E (D j) := fun j => (gED j).toAlgebra
  let _ : (j : ι) → SMul E (D j) := fun j => (aED j).toSMul
  let _ : (j : ι) → Module E (D j) := fun j =>
    @Algebra.toModule E (D j) _ _ (aED j)
  have halgebraMap_eq_original_fraction_lift (j : ι) :
      algebraMap E (D j) = IsFractionRing.lift (K := E) (hinj j) :=
    hcoordinate_eq_original_fraction_lift j
  let : ∀ j : ι, IsScalarTower S E (D j) := fun j =>
    IsScalarTower.of_algebraMap_eq fun s => by
      change algebraMap S (D j) s =
        epsilon.toFun ((1 : L) ⊗ₜ[F] algebraMap S E s) j
      exact (IsScalarTower.algebraMap_apply S (U j) (D j) s).trans
        (hintegral s j).symm
  have hinjSU (j : ι) : Function.Injective (algebraMap S (U j)) := by
    intro s t h
    apply hinj j
    simpa only [← IsScalarTower.algebraMap_apply S (U j) (D j)] using
      congrArg (algebraMap (U j) (D j)) h
  let : ∀ j : ι, FaithfulSMul S (U j) := fun j =>
    (faithfulSMul_iff_algebraMap_injective S (U j)).mpr (hinjSU j)
  have hcoordinate (e : E) (j : ι) :
      epsilon.toFun ((1 : L) ⊗ₜ[F] e) j = algebraMap E (D j) e := rfl
  have hsource (e : E) (j : ι) :=
    (hright e j).symm.trans (hcoordinate e j)
  have hbranchMixed :=
    mem_mixedSpan_of_tensor_coordinates K M L E D delta hsource n x hmixed
  exact ramification_smul_restrict_norm_residue_difference_eq_zero_of_unramified_mixed_branches
    R S T F E L U D epsilon hcoordinate hbranchone hp n x hbranchMixed

end Stacks.Chow
