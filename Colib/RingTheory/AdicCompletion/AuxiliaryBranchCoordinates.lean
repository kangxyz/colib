/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.FractionBranches
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFactorPackage
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Native auxiliary coordinates over specified normalization rings

This extracts the coordinate-producing part of
`exists_auxiliaryBranchTensorEquiv_of_dedekind_normalization`. The DVR `B` and its finite
Dedekind algebra `C` are parameters, not closed integral-closure expressions. The source map
`S → C` is the existing map supplied by the caller. Its two integral compatibility facts are
the scalar tower into `M` and the original commuting square from `R`.

The proof constructs the tensor equivalence by base changing `eta` and composing with the
original `fractionTensorEquivLocalFractionFields`. It then proves the integral coordinates,
all branch-local source maps, injectivity, and equality with the native source fraction lift.
No completed coordinate, ramification index, norm square, or separability assumption is input.
The native completion and fraction-field structure telescope is copied from the completed
branch consumer. Unused henselian and residue-characteristic conclusions are omitted.

Proof provenance: the coordinate-producing part of
`AuxiliaryBranchMapsFiniteNormalization.lean`, SHA-256
`be6603c56f88cdd4651219730e0db0bc1a2bad4163b66d6545b7834666a2d6a7`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe uR uS uF uE uB uC uK uM

namespace AdicCompletion

open IsLocalRing

attribute [local irreducible] UniqueFactorizationMonoid.normalizedFactors
  UniqueFactorizationMonoid.factors

/-- Produce the original completed tensor and source-fraction coordinates over the specified
DVR and finite Dedekind algebra. Both source-map compatibility inputs concern integral maps. -/
theorem exists_auxiliaryBranchTensorEquiv_of_native_normalization
    (R : Type uR) (S : Type uS) (F : Type uF) (E : Type uE)
    (B : Type uB) (C : Type uC) (K : Type uK) (M : Type uM)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsDiscreteValuationRing.IsExtension R S]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra S E] [IsFractionRing S E] [Algebra F E]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    [CommRing C] [IsDedekindDomain C] [Algebra B C] [Algebra S C]
    [Module.Finite B C] [Module.IsTorsionFree B C] [DecidableEq (Ideal C)]
    [Field K] [Algebra R K] [Algebra B K] [IsFractionRing B K]
    [Algebra F K] [IsScalarTower R F K] [IsScalarTower R B K]
    [Field M] [Algebra B M] [Algebra C M] [IsScalarTower B C M] [IsFractionRing C M]
    [Algebra K M] [IsScalarTower B K M]
    [Algebra S M] [Algebra E M] [IsScalarTower S E M] [IsScalarTower S C M]
    (hsource : ∀ r : R, algebraMap B C (algebraMap R B r) =
      algebraMap S C (algebraMap R S r))
    (eta : K ⊗[F] E ≃ₐ[K] M)
    (heta : ∀ e : E, eta (1 ⊗ₜ[F] e) = algebraMap E M e) :
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
    ∃ epsilon : L ⊗[F] E ≃ₐ[L] ∀ j : IdealBranch J, D j,
      IsScalarTower R F L ∧
      (∀ (e : E) (j : IdealBranch J), epsilon (1 ⊗ₜ[F] e) j =
        delta.toFun ((1 : L) ⊗ₜ[K] algebraMap E M e) j) ∧
      (∀ (k : K) (j : IdealBranch J),
        delta.toFun ((1 : L) ⊗ₜ[K] algebraMap K M k) j =
          algebraMap L (D j) (algebraMap K L k)) ∧
      (∀ (s : S) (j : IdealBranch J),
        epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
          algebraMap (U j) (D j) (algebraMap S (U j) s)) ∧
      (∀ j : IdealBranch J, IsScalarTower R S (U j) ∧
        IsScalarTower R T (U j) ∧ IsLocalHom (algebraMap S (U j))) ∧
      ∃ hinj : ∀ j : IdealBranch J, Function.Injective (algebraMap S (D j)),
        ∀ j : IdealBranch J,
          ((Pi.evalRingHom D j).comp
              (epsilon.toRingHom.comp
                (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E).toRingHom) =
            IsFractionRing.lift (K := E) (hinj j)) ∧
          (let _ : Algebra E (D j) := (IsFractionRing.lift (K := E) (hinj j)).toAlgebra
           let _ : SMul E (D j) := Algebra.toSMul
           IsScalarTower S E (D j)) := by
  classical
  intro J T L U _ _ D _ _ _ _ delta _ _ _ _ _ _ _ aTU _ _ aLD _
  have : IsScalarTower B K L := fractionCompletionIsScalarTower B K
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B L,
      IsScalarTower.algebraMap_apply B K L,
      ← IsScalarTower.algebraMap_apply R B K]
  have hRFL : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R F K,
      ← IsScalarTower.algebraMap_apply F K L]
  let epsilon : L ⊗[F] E ≃ₐ[L] ∀ j : IdealBranch J, D j :=
    (Algebra.TensorProduct.cancelBaseChange F K L L E).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) eta).trans delta)
  have hepsilon (e : E) (j : IdealBranch J) :
      epsilon (1 ⊗ₜ[F] e) j = delta (1 ⊗ₜ[K] algebraMap E M e) j := by
    simp only [epsilon, AlgEquiv.trans_apply,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, heta]
  have hauxiliary (k : K) (j : IdealBranch J) :
      delta (1 ⊗ₜ[K] algebraMap K M k) j =
        algebraMap L (D j) (algebraMap K L k) := by
    have h : (1 : L) ⊗ₜ[K] algebraMap K M k =
        algebraMap L (L ⊗[K] M) (algebraMap K L k) := by
      rw [← Algebra.TensorProduct.algebraMap_apply',
        IsScalarTower.algebraMap_apply K L (L ⊗[K] M)]
    rw [h, delta.commutes]
    rfl
  have hintegral (s : S) (j : IdealBranch J) :
      epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
        algebraMap (U j) (D j) (algebraMap S (U j) s) := by
    rw [hepsilon, ← IsScalarTower.algebraMap_apply S E M,
      IsScalarTower.algebraMap_apply S C M]
    change fractionTensorEquivLocalFractionFields B C K M
      (1 ⊗ₜ[K] algebraMap C M (algebraMap S C s)) j = _
    rw [fractionTensorEquivLocalFractionFields_one_tmul]
    rw [← IsScalarTower.algebraMap_apply C (Localization.AtPrime j.val) (U j),
      ← IsScalarTower.algebraMap_apply S C (U j)]
  have hsourceTower (j : IdealBranch J) : IsScalarTower R S (U j) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R B (U j),
        IsScalarTower.algebraMap_apply B C (U j),
        hsource r,
        ← IsScalarTower.algebraMap_apply S C (U j)]
  have hcompletedTower (j : IdealBranch J) : IsScalarTower R T (U j) := by
    have := localCompletionBaseIsScalarTower (S := C) (maximalIdeal B) j
    exact IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R B (U j),
        IsScalarTower.algebraMap_apply B T (U j),
        ← IsScalarTower.algebraMap_apply R B T]
  have hlocal (j : IdealBranch J) : IsLocalHom (algebraMap S (U j)) := by
    have : IsLocalHom (algebraMap B (U j)) := by
      rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime j.val) (U j)]
      infer_instance
    have : IsLocalHom (algebraMap R (U j)) := by
      rw [IsScalarTower.algebraMap_eq R B (U j)]
      infer_instance
    have := hsourceTower j
    exact Stacks.EppTheorem.isLocalHom_algebraMap_of_tower R S (U j)
  have hinjSM : Function.Injective (algebraMap S M) := by
    rw [IsScalarTower.algebraMap_eq S E M]
    exact (algebraMap E M).injective.comp (IsFractionRing.injective S E)
  have hinjSC : Function.Injective (algebraMap S C) := by
    intro s t h
    apply hinjSM
    simpa only [← IsScalarTower.algebraMap_apply S C M] using
      congrArg (algebraMap C M) h
  have hinjSU (j : IdealBranch J) : Function.Injective (algebraMap S (U j)) := by
    rw [IsScalarTower.algebraMap_eq S C (U j)]
    exact (branchCompletion_algebraMap_injective J j).comp hinjSC
  have hinjSD (j : IdealBranch J) : Function.Injective (algebraMap S (D j)) := by
    rw [IsScalarTower.algebraMap_eq S (U j) (D j)]
    exact (IsFractionRing.injective (U j) (D j)).comp (hinjSU j)
  refine ⟨epsilon, hRFL, hepsilon, hauxiliary, hintegral,
    fun j => ⟨hsourceTower j, hcompletedTower j, hlocal j⟩, hinjSD, ?_⟩
  intro j
  refine ⟨?_, ?_⟩
  · apply IsFractionRing.ringHom_ext (A := S)
    intro s
    change epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
      IsFractionRing.lift (K := E) (hinjSD j) (algebraMap S E s)
    rw [hintegral, IsFractionRing.lift_algebraMap,
      ← IsScalarTower.algebraMap_apply S (U j) (D j)]
  · intro _ _
    exact IsScalarTower.of_algebraMap_eq (R := S) (S := E) (A := D j) fun s =>
      (IsFractionRing.lift_algebraMap (K := E) (hinjSD j) s).symm

end AdicCompletion
