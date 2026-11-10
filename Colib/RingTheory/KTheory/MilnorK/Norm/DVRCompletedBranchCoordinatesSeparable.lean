/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.EtaleBranches
public import Colib.RingTheory.AdicCompletion.FractionBranches
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRBranchCoordinatesSeparable

/-!
# Weighted error on the original completed finite-etale branches

The normalization rings B and C are abstract here, while the branches are the original
localizations, adic completions and native fraction fields. The full completion tensor
coordinates, source fraction maps and six native structure parents agree with the actual
auxiliary branch construction.

Finite etaleness of the original C over B proves every completed branch index is one.
The conversion to the abstract-field weighted coordinate theorem is performed at this
layer, before specializing C to a large actual integral closure. No completed branch is
selected and no norm-square premise, auxiliary separability or replacement model is used.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.Chow

open DiscreteValuationRing.Ramification _root_.AdicCompletion

attribute [local irreducible] UniqueFactorizationMonoid.normalizedFactors
  UniqueFactorizationMonoid.factors

/-- The original finite-etale completed branches annihilate the weighted norm-residue error
of one auxiliary mixed witness. Their complete native tensor and source fraction coordinates
are the interface; branch index one is proved internally from finite etaleness. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero_of_etale_completed_coordinates
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
          (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
            milnorKNorm (ResidueField R) (ResidueField S) n
              (dvrMilnorTameSymbol' S E n x)) = 0 := by
  classical
  intro J T L U _ _ D _ _ _ _ delta _ _ _ _ _ _ _ aTU _ _ aLD _
    _ _ epsilon hRFL hright hintegral htowers hinj hfraction hp n x hmixed
  let _ : (j : IdealBranch J) → SMul L (D j) := fun j => (aLD j).toSMul
  let _ : (j : IdealBranch J) → Module L (D j) := fun j =>
    @Algebra.toModule L (D j) _ _ (aLD j)
  let : IsScalarTower R F L := hRFL
  let : ∀ j : IdealBranch J, IsScalarTower R S (U j) := fun j => (htowers j).1
  let : ∀ j : IdealBranch J, IsScalarTower R T (U j) := fun j => (htowers j).2.1
  let : ∀ j : IdealBranch J, IsLocalHom (algebraMap S (U j)) :=
    fun j => (htowers j).2.2
  let : ∀ j : IdealBranch J, Module.Finite T (U j) :=
    fun j => (localCompletionBaseFiniteEtale B C j).1
  let : ∀ j : IdealBranch J, IsLocalHom (algebraMap T (U j)) :=
    fun j => localCompletionBase_isLocalHom B C j
  let : ∀ j : IdealBranch J, FaithfulSMul T (U j) :=
    fun j => localCompletionBaseFaithfulSMul B C j
  let : ∀ j : IdealBranch J, Module.IsTorsionFree T (U j) := fun j =>
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective T (U j))
  let : ∀ j : IdealBranch J, IsScalarTower T L (D j) :=
    fun j => localCompletionFractionIsScalarTower B C j
  let : ∀ j : IdealBranch J, FiniteDimensional L (D j) :=
    fun j => localCompletionFractionFinite B C j
  let : ∀ j : IdealBranch J, IsScalarTower S (U j) (D j) := fun j =>
    OreLocalization.instIsScalarTower
      (R := S) (R' := U j) (M := U j) (X := U j) (S := nonZeroDivisors (U j))
  have hbranchone (j : IdealBranch J) : ramificationIdx T (U j) = 1 :=
    localCompletion_ramificationIdx_eq_one_of_etale B C j
  set_option backward.isDefEq.respectTransparency false in
    with_reducible_and_instances
      exact ramification_smul_restrict_norm_residue_difference_eq_zero_of_auxiliary_coordinates
        R S T F E L K M U D epsilon delta hinj hfraction hright hintegral hbranchone hp n x hmixed

end Stacks.Chow
