/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePGroup
public import Colib.RingTheory.AdjoinRoot.ScalarBranchAlgebra
public import Colib.RingTheory.IntegralClosure.CompleteTower

/-!
# Actual complete-DVR diagrams for every scalar branch

The coefficient polynomial may split into any number of branches. Each old-root
map is the original `AdjoinRoot.map`; both upper ring maps are its literal
restrictions to integral closures. The upper DVR remains the closure of the
original base, also when it is viewed over the coefficient DVR.

Adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/CompleteScalarBranch.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 39–177.
Only the old factor index and Milnor model are replaced by the existing native
factor subtype, chosen norm and canonical tame symbol.
-/

@[expose] public noncomputable section

namespace Stacks.Chow.CompleteScalarBranch

open Polynomial MonicIrreducibleOfDegree IsLocalRing AdjoinRoot
open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower

universe u

attribute [local instance] AdjoinRoot.scalarBranchAlgebra closureAlgebra
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

section Maps

variable (R : Type*) {F L : Type*} [CommRing R] [Field F] [Field L]
  [Algebra F L] [Algebra R F] [Algebra R L] [IsScalarTower R F L]
  {d : ℕ} (p : MonicIrreducibleOfDegree F d)
  (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
    poly r.2 ∣ (poly p).map (algebraMap F L)})

/-- The old-root action is exactly the quotient map for this coefficient branch. -/
theorem branch_algebraMap_eq :
    algebraMap (AdjoinRoot (poly p)) (AdjoinRoot (poly r.1.2)) =
      AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2 := rfl

/-- The original base ring commutes with the literal old-root branch map. -/
instance baseBranchTower : IsScalarTower R (AdjoinRoot (poly p)) (AdjoinRoot (poly r.1.2)) := by
  have : IsScalarTower F (AdjoinRoot (poly p)) (AdjoinRoot (poly r.1.2)) :=
    AdjoinRoot.scalarBranchBaseTower (poly p) r
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [IsScalarTower.algebraMap_apply R F (AdjoinRoot (poly p)),
    ← IsScalarTower.algebraMap_apply F (AdjoinRoot (poly p)) (AdjoinRoot (poly r.1.2)),
    ← IsScalarTower.algebraMap_apply R F (AdjoinRoot (poly r.1.2))]

/-- The actual integral-closure map has precisely the old-root quotient values. -/
theorem oldRoot_closureMap_apply (s : integralClosure R (AdjoinRoot (poly p))) :
    algebraMap (integralClosure R (AdjoinRoot (poly r.1.2))) (AdjoinRoot (poly r.1.2))
      (algebraMap (integralClosure R (AdjoinRoot (poly p)))
        (integralClosure R (AdjoinRoot (poly r.1.2))) s) =
      AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2
        (algebraMap (integralClosure R (AdjoinRoot (poly p))) (AdjoinRoot (poly p)) s) := rfl

omit [Algebra R F] [IsScalarTower R F L] in
/-- The coefficient map also remains the original field inclusion on integral elements. -/
theorem coefficient_closureMap_apply (t : integralClosure R L) :
    algebraMap (integralClosure R (AdjoinRoot (poly r.1.2))) (AdjoinRoot (poly r.1.2))
      (algebraMap (integralClosure R L) (integralClosure R (AdjoinRoot (poly r.1.2))) t) =
      algebraMap L (AdjoinRoot (poly r.1.2)) (algebraMap (integralClosure R L) L t) := rfl

/-- No new upper ring is introduced over the old-root integral closure. -/
theorem oldRoot_isIntegralClosure :
    IsIntegralClosure (integralClosure R (AdjoinRoot (poly r.1.2)))
      (integralClosure R (AdjoinRoot (poly p))) (AdjoinRoot (poly r.1.2)) :=
  upper_isIntegralClosure R (AdjoinRoot (poly p)) (AdjoinRoot (poly r.1.2))

omit [Algebra R F] [IsScalarTower R F L] in
/-- No new upper ring is introduced over the coefficient integral closure. -/
theorem coefficient_isIntegralClosure :
    IsIntegralClosure (integralClosure R (AdjoinRoot (poly r.1.2)))
      (integralClosure R L) (AdjoinRoot (poly r.1.2)) :=
  upper_isIntegralClosure R L (AdjoinRoot (poly r.1.2))

/-- The old-root ring map is local, without imposing unramifiedness. -/
theorem oldRoot_isLocalHom :
    IsLocalHom (algebraMap (integralClosure R (AdjoinRoot (poly p)))
      (integralClosure R (AdjoinRoot (poly r.1.2)))) :=
  upper_isLocalHom R (AdjoinRoot (poly p)) (AdjoinRoot (poly r.1.2))

omit [Algebra R F] [IsScalarTower R F L] in
/-- The coefficient ring map is local, without imposing unramifiedness. -/
theorem coefficient_isLocalHom :
    IsLocalHom (algebraMap (integralClosure R L) (integralClosure R (AdjoinRoot (poly r.1.2)))) :=
  upper_isLocalHom R L (AdjoinRoot (poly r.1.2))

end Maps

section Finiteness

variable (R F L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
  {d : ℕ} (p : MonicIrreducibleOfDegree F d)
  (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
    poly r.2 ∣ (poly p).map (algebraMap F L)})

/-- Every scalar-branch integral closure is finite over the actual old-root closure. -/
theorem oldRoot_finite :
    Module.Finite (integralClosure R (AdjoinRoot (poly p)))
      (integralClosure R (AdjoinRoot (poly r.1.2))) := by
  have : FiniteDimensional L (AdjoinRoot (poly r.1.2)) :=
    (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  have : FiniteDimensional F (AdjoinRoot (poly r.1.2)) := Module.Finite.trans L _
  exact upper_finite R F (AdjoinRoot (poly p)) (AdjoinRoot (poly r.1.2))

/-- Every scalar-branch integral closure is finite over the actual coefficient closure. -/
theorem coefficient_finite :
    Module.Finite (integralClosure R L) (integralClosure R (AdjoinRoot (poly r.1.2))) := by
  have : FiniteDimensional L (AdjoinRoot (poly r.1.2)) :=
    (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  have : FiniteDimensional F (AdjoinRoot (poly r.1.2)) := Module.Finite.trans L _
  exact upper_finite R F L (AdjoinRoot (poly r.1.2))

end Finiteness

section Complete

variable (R F L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
  {d : ℕ} (p : MonicIrreducibleOfDegree F d)
  (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
    poly r.2 ∣ (poly p).map (algebraMap F L)})

/-- Every branch embedded in a Galois p-group ambient satisfies the actual
coefficient norm-residue square. All structures on both closure DVRs are derived. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete_scalarBranch_of_pGroup
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : AdjoinRoot (poly r.1.2) →ₐ[L] Ω) (n : ℕ)
    (x : MilnorKTheory (AdjoinRoot (poly r.1.2)) (n + 1)) :
    let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
    let _ : FiniteDimensional L (AdjoinRoot (poly r.1.2)) :=
      (AdjoinRoot.powerBasis' (monic r.1.2)).finite
    let _ : FiniteDimensional F (AdjoinRoot (poly r.1.2)) := Module.Finite.trans L _
    let _ := integralClosure_isDiscreteValuationRing R F L
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot (poly r.1.2))
    let _ := integralClosure_isLocalHom R F L
    let _ := coefficient_isLocalHom R p r
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly r.1.2))
      (integralClosure R (AdjoinRoot (poly r.1.2)))
    let _ := coefficient_finite R F L p r
    let _ : CharZero (ResidueField (integralClosure R L)) :=
      charZero_of_injective_algebraMap
        (algebraMap (ResidueField R) (ResidueField (integralClosure R L))).injective
    dvrMilnorTameSymbol' (integralClosure R L) L n
        (milnorKNorm L (AdjoinRoot (poly r.1.2)) (n + 1) x) =
      milnorKNorm (ResidueField (integralClosure R L))
        (ResidueField (integralClosure R (AdjoinRoot (poly r.1.2)))) n
        (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly r.1.2)))
          (AdjoinRoot (poly r.1.2)) n x) := by
  dsimp only
  let D := AdjoinRoot (poly r.1.2)
  let T := integralClosure R L
  let U := integralClosure R D
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  have : CharZero D := charZero_of_injective_algebraMap (algebraMap L D).injective
  have : FiniteDimensional L D := (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  have : FiniteDimensional F D := Module.Finite.trans L D
  have : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing R F L
  have : IsDiscreteValuationRing U := integralClosure_isDiscreteValuationRing R F D
  have : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F L
  have : IsLocalHom (algebraMap T U) := coefficient_isLocalHom R p r
  have : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  have : IsFractionRing U D := IsIntegralClosure.isFractionRing_of_finite_extension R F D U
  have : Module.Finite T U := coefficient_finite R F L p r
  have : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete R F L
  have : CharZero (ResidueField T) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField T)).injective
  have : IsScalarTower R T U := baseTower R L D
  have : @IsScalarTower T U D _ _ (AdjoinRoot.instSMulAdjoinRoot (S := T) (poly r.1.2)) := by
    let branchCoefficientAlgebra : Algebra T D := AdjoinRoot.instAlgebra (S := T) (poly r.1.2)
    exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsIntegralClosure U T D := coefficient_isIntegralClosure R p r
  exact dvrMilnorTameSymbol'_milnorKNorm_complete_of_pGroup T U L D Ω ℓ hG g n x

end Complete

end Stacks.Chow.CompleteScalarBranch

end
