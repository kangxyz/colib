/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.InfinityTwist
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVR
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Every original infinity branch in a finite rational-function extension

Adapted from Aglib `Norm/FiniteExtension/InfinityBranches.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 32–97. The integral closure
is taken in the original E with its actual inverted scalar action. Every
normalized ideal factor above the original origin maximal ideal contributes its
actual localized tame symbol followed by its native residue-field norm.
No completion field, replacement point or branch-compatibility premise occurs.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial IsLocalRing _root_.AdicCompletion

universe u
variable (k E : Type u) [Field k] [CharZero k] [Field E]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E]

/-- The normed tame residues at all actual branches of the normalization at infinity. -/
def infinityBranchResidueSum (n : ℕ) (x : MilnorKTheory E (n + 1)) : MilnorKTheory k n := by
  classical
  let fin := infinityTwistFinite k E
  letI := infinityTwistAlgebra k E
  letI := fin
  let R := localRingAtOrigin k
  letI : Algebra R E := ((algebraMap (RatFunc k) E).comp (algebraMap R (RatFunc k))).toAlgebra
  letI : IsScalarTower R (RatFunc k) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.IsTorsionFree R E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap (RatFunc k) E).injective.comp (IsFractionRing.injective R (RatFunc k)))
  let S : Type u := integralClosure R E
  letI : CommRing S := inferInstance
  letI : IsDedekindDomain S := integralClosure.isDedekindDomain R (RatFunc k) E
  letI : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R E (A := S)
  letI : Module.Finite R S := IsIntegralClosure.finite R (RatFunc k) E S
  letI : IsFractionRing S E :=
    IsIntegralClosure.isFractionRing_of_finite_extension R (RatFunc k) E S
  letI : CharZero (ResidueField R) := (residueFieldAtOriginEquiv k).symm.toRingHom.charZero
  let J := (maximalIdeal R).map (algebraMap R S)
  letI := fun q : IdealBranch (R := S) J => originalBranchFractionAlgebra S E q
  letI := fun q : IdealBranch (R := S) J => originalBranchIsFractionRing S E q
  refine milnorKTransport (residueFieldAtOriginEquiv k).symm.toRingHom n
    (∑ q : IdealBranch (R := S) J, ?_)
  letI := originalBranchResidueFinite R S q
  exact milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
    (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n x)

/-- The actual original norm's infinity residue equals the sum over every original branch. -/
theorem infinityResidue_milnorKNorm (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    infinityResidue (k := k) n (milnorKNorm (RatFunc k) E (n + 1) x) =
      infinityBranchResidueSum k E n x := by
  rw [infinityResidue_milnorKNorm_eq_twist]
  classical
  let fin := infinityTwistFinite k E
  let := infinityTwistAlgebra k E
  let := fin
  let R := localRingAtOrigin k
  let : Algebra R E := ((algebraMap (RatFunc k) E).comp (algebraMap R (RatFunc k))).toAlgebra
  let : IsScalarTower R (RatFunc k) E := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.IsTorsionFree R E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap (RatFunc k) E).injective.comp (IsFractionRing.injective R (RatFunc k)))
  let S : Type u := integralClosure R E
  let : CommRing S := inferInstance
  let : IsDedekindDomain S := integralClosure.isDedekindDomain R (RatFunc k) E
  let : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R E (A := S)
  let : Module.Finite R S := IsIntegralClosure.finite R (RatFunc k) E S
  let : IsFractionRing S E :=
    IsIntegralClosure.isFractionRing_of_finite_extension R (RatFunc k) E S
  let : CharZero (ResidueField R) := (residueFieldAtOriginEquiv k).symm.toRingHom.charZero
  let J := (maximalIdeal R).map (algebraMap R S)
  let := fun q : IdealBranch (R := S) J => originalBranchFractionAlgebra S E q
  let := fun q : IdealBranch (R := S) J => originalBranchIsFractionRing S E q
  change milnorKTransport (residueFieldAtOriginEquiv k).symm.toRingHom n
    (dvrMilnorTameSymbol' R (RatFunc k) n (milnorKNorm (RatFunc k) E (n + 1) x)) = _
  exact congrArg (milnorKTransport (residueFieldAtOriginEquiv k).symm.toRingHom n)
    (dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches R S (RatFunc k) E n x)

end Stacks.Chow
