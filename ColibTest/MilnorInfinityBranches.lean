/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.InfinityBranches

/-! Full-statement consumers of the actual inverted action and every infinity branch.
These are source examples, not executed validation. -/

noncomputable section

open Stacks.Chow Polynomial IsLocalRing _root_.AdicCompletion _root_.AlgebraicGeometry

universe u
variable (k E : Type u) [Field k] [CharZero k] [Field E]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E]

example (a : RatFunc k) :
    @algebraMap (RatFunc k) E _ _ (infinityTwistAlgebra k E) a =
      algebraMap (RatFunc k) E (projectiveLineChartInversion k a) := rfl

example : @FiniteDimensional (RatFunc k) E _ _ (infinityTwistAlgebra k E).toModule :=
  infinityTwistFinite k E

example (n : ℕ) (x : MilnorKTheory E n) :
    infinityTwistNorm k E n x =
      milnorKTransport (projectiveLineChartInversion k).toRingHom n
        (milnorKNorm (RatFunc k) E n x) :=
  infinityTwistNorm_eq k E n x

example (x : MilnorKTheory E 0) :
    infinityTwistNorm k E 0 x =
      milnorKTransport (projectiveLineChartInversion k).toRingHom 0
        (milnorKNorm (RatFunc k) E 0 x) :=
  infinityTwistNorm_eq k E 0 x

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    infinityResidue (k := k) n (milnorKNorm (RatFunc k) E (n + 1) x) =
      infinityBranchResidueSum k E n x :=
  infinityResidue_milnorKNorm k E n x

example (x : MilnorKTheory E 1) :
    infinityResidue (k := k) 0 (milnorKNorm (RatFunc k) E 1 x) =
      infinityBranchResidueSum k E 0 x :=
  infinityResidue_milnorKNorm k E 0 x

/- The sum's full original normalization and localization data, without an abstract branch input. -/
example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    let originalSum := infinityBranchResidueSum k E n x
    let fin := infinityTwistFinite k E
    let := infinityTwistAlgebra k E
    let := fin
    let R := localRingAtOrigin k
    let : Algebra R E :=
      ((algebraMap (RatFunc k) E).comp (algebraMap R (RatFunc k))).toAlgebra
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
    originalSum =
      milnorKTransport (residueFieldAtOriginEquiv k).symm.toRingHom n
        (∑ q : IdealBranch (R := S) J,
          letI := originalBranchResidueFinite R S q
          milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
            (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n x)) := by
  rfl
