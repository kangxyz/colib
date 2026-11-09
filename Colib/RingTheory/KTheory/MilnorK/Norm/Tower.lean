/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.NestedScalarTower
public import Colib.RingTheory.KTheory.MilnorK.RestrictionSylow
public import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Unrestricted native simple-norm towers in characteristic zero

The actual splitting field of the original top polynomial is finite Galois.
Over each actual Sylow fixed field, the complete nested-factor calculation
proves the restricted tower identity. Native finite-restriction detection then
descends the equality to the original base. Neither presentation independence
nor arbitrary branch norm compatibility is an input.

The result retains the given embedding, the canonical relative tower factor,
both original quotient maps, and the native whole Milnor rings. The lower
extension need not be normal or of prime degree, and no ambient field is an
input to the final endpoints.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The actual native simple-norm tower for any specified embedding in characteristic zero. -/
theorem simpleMilnorNorm_tower
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (x : MilnorKRing (AdjoinRoot (poly (Sigma.snd (Subtype.val (AdjoinRoot.towerFactor (poly p)
      (poly h) f)))))) :
    simpleMilnorNorm p (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2 x) =
      simpleMilnorNorm h (milnorKRingMap ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
      f)).toRingHom x) := by
  classical
  let Ω := (poly h).SplittingField
  let hGalois : IsGalois k Ω :=
    IsGalois.of_separable_splitting_field (irreducible h).separable
  apply eq_of_milnorKRingMap_sylow_restrictions k Ω
  intro ℓ hℓ
  let hPrime : Fact ℓ.Prime := ⟨hℓ⟩
  let S : Sylow ℓ (Ω ≃ₐ[k] Ω) := Classical.arbitrary _
  refine ⟨S, ?_⟩
  exact simpleMilnorNorm_tower_map_of_pGroup_splitting
    (K := IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))
    p h f ℓ (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ S)
    (Polynomial.SplittingField.splits (poly h)) x

/-- On the original top field, the native simple norm is the composite through
the given lower field and the literal inverse coefficient-factor map. -/
theorem simpleMilnorNorm_eq_tower
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (x : MilnorKRing (AdjoinRoot (poly h))) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p))) (poly h) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (AdjoinRoot.towerFactor (poly p) (poly h)
      f).2) x)) := by
  let T := AdjoinRoot (poly h)
  let θ := AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f
  rw [simpleMilnorNorm_tower p h f]
  apply congrArg (simpleMilnorNorm h)
  rw [← AdjoinRoot.towerFactorRingEquiv_symm_toRingHom, milnorKRingMap_comp_apply]
  have hcomp : (θ).toRingHom.comp (θ).symm.toRingHom = RingHom.id T := by
    apply RingHom.ext
    intro a
    exact (θ).apply_symm_apply a
  exact ((congrArg (fun ψ : T →+* T => milnorKRingMap ψ x) hcomp).trans
    (milnorKRingMap_id_apply x)).symm

/-- Equality of the native additive maps on the actual upper quotient. -/
theorem simpleMilnorNorm_comp_simpleMilnorNorm_tower
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) :
    (simpleMilnorNorm p).comp (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) =
      (simpleMilnorNorm h).comp (milnorKRingMap ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
      f)).toRingHom).toAddMonoidHom := by
  ext x
  exact simpleMilnorNorm_tower p h f x

/-- Equality of the native additive maps on the original top field. -/
theorem simpleMilnorNorm_eq_comp_tower
    {k : Type u} [Field k] [CharZero k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) :
    simpleMilnorNorm h =
      (simpleMilnorNorm p).comp
        ((simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2).comp
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p))) (poly h) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (AdjoinRoot.towerFactor (poly p) (poly h)
      f).2)).toAddMonoidHom) := by
  ext x
  exact simpleMilnorNorm_eq_tower p h f x

end Stacks.Chow

end
