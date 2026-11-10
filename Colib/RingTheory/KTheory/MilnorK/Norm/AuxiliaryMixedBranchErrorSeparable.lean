/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.EtaleNormalization
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRNativeAuxiliaryCoordinatesSeparable

/-!
# The actual auxiliary error for a separable constant cover

A finite auxiliary extension with native Dedekind normalization is allowed to be
inseparable. The top mapped-root cover is identified by its actual constant
polynomial presentation. This proves finite étaleness of every native upper
normalization and ramification index one for every original completed branch.
One actual mixed witness then kills the ramification-weighted restriction of the
original norm-residue error at every base branch.

For the power-series base, the native Japanese normalization theorem supplies
the Dedekind condition with no auxiliary separability premise. The original
residue extension is assumed separable, as independently proved for the actual
separable constant Laurent cover. There is no norm-compatibility premise, branch
index-one premise, selected branch or replacement norm/map/carrier.

This is the branchwise error identity. Retraction and coprime cancellation are
separate steps, so this file does not yet assert the full Laurent square.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial
open scoped TensorProduct

universe u

namespace Stacks.Chow

open DiscreteValuationRing.Ramification _root_.AdicCompletion

-- Keep the native branch-index factorization opaque during instance synthesis.
attribute [local irreducible] UniqueFactorizationMonoid.normalizedFactors
  UniqueFactorizationMonoid.factors

set_option maxHeartbeats 400000 in
-- Specializing the full native iterated branch construction checks a large dependent proof.
/-- One actual finite auxiliary mixed witness makes the ramification weight kill the
restricted original norm-residue error at every actual completed base branch. The full
upper branch family and every mixed membership are constructed inside the proof. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero_of_separable_constant_cover
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
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  classical
  intro A _ _ _ _ i T _
  let : IsDiscreteValuationRing.IsExtension R S := ⟨⟩
  let : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension F K
  have : Module.IsTorsionFree R K := Module.IsTorsionFree.trans_faithfulSMul R F K
  have : Module.IsTorsionFree R A := IsIntegralClosure.isTorsionFree R K
  let B := Localization.AtPrime i.val
  let _ : CommRing B := inferInstance
  let _ : CommSemiring B := CommRing.toCommSemiring
  have : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr (by
    rw [IsScalarTower.algebraMap_eq R A T]
    exact (branchCompletion_algebraMap_injective _ i).comp
      (FaithfulSMul.algebraMap_injective R A))
  let := originalBranchFractionAlgebra A K i
  have := originalBranchFractionTower A K i
  let := originalBranchIsFractionRing A K i
  have : FaithfulSMul B K :=
    (faithfulSMul_iff_algebraMap_injective B K).mpr (IsFractionRing.injective B K)
  have : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A K,
      IsScalarTower.algebraMap_apply R A B,
      ← IsScalarTower.algebraMap_apply A B K]
  let : Algebra B M := ((algebraMap K M).comp (algebraMap B K)).toAlgebra
  have : IsScalarTower B K M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R B M := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K M,
      IsScalarTower.algebraMap_apply R B K,
      ← IsScalarTower.algebraMap_apply B K M]
  let : Algebra k B := ((algebraMap R B).comp (algebraMap k R)).toAlgebra
  let _ : SMul k B := Algebra.toSMul
  let _ : Module k B := Algebra.toModule
  have : IsScalarTower k B K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap k K a = algebraMap B K (algebraMap R B (algebraMap k R a))
    rw [← IsScalarTower.algebraMap_apply R B K,
      ← IsScalarTower.algebraMap_apply k R K]
  let C : Type u := integralClosure B M
  let _ : CommRing C := inferInstance
  let _ : CommSemiring C := CommRing.toCommSemiring
  let : IsDedekindDomain C := integralClosure.isDedekindDomain B K M
  have : Module.Finite B C := IsIntegralClosure.finite B K M C
  let : Algebra.Etale B C :=
    (AdjoinRoot.finite_etale_integralClosure_constant_factor k B K M hmonic hsep
      econstant.toAlgHom econstant.surjective).2
  have : Module.IsTorsionFree B M := Module.IsTorsionFree.trans_faithfulSMul B K M
  have : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B M
  let : IsFractionRing C M := integralClosure.isFractionRing_of_finite_extension K M
  let : DecidableEq (Ideal C) := Classical.decEq _
  let : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S C := Stacks.EppTheorem.algebraIntegralClosureBase R B S M
  have : IsScalarTower S C M :=
    Stacks.EppTheorem.isScalarTower_base_integralClosure_factor R B S M
  have hsource (r : R) : algebraMap B C (algebraMap R B r) =
      algebraMap S C (algebraMap R S r) :=
    Stacks.EppTheorem.algebraMap_integralClosureBase_eq R B S M r
  exact ramification_smul_restrict_norm_residue_difference_eq_zero_of_etale_auxiliary_tensor
    R S F E B C K M hsource eta heta hp n x hmixed

end Stacks.Chow
