/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenRecursion
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerFinite
public import Colib.RingTheory.KTheory.MilnorK.Norm.AdjoinSimpleEquivarianceAcross
public import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleEquivarianceAcross

/-!
# Simultaneous transport of the native chosen norm

The source calculation uses the literal selected simple step. Its image
under the compatible pair of field equivalences is a permitted simple
step on the target, and the remaining field degree is smaller.
-/

@[expose] public noncomputable section

open IntermediateField Module

universe u v

namespace Stacks.Chow

private theorem norm_equivariance_of_bijective
    {K L : Type u} {K' L' : Type v} [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
    (σ : K ≃+* K') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap K L) = (algebraMap K' L').comp σ.toRingHom)
    (hK : Function.Bijective (algebraMap K L)) (x : MilnorKRing L) :
    milnorKRingMapLift σ.toRingHom (milnorKNormRing K L x) =
      milnorKNormRing K' L' (milnorKRingMapLift τ.toRingHom x) := by
  have hK' : Function.Bijective (algebraMap K' L') := by
    refine ⟨(algebraMap K' L').injective, ?_⟩
    intro y
    obtain ⟨z, rfl⟩ := τ.surjective y
    obtain ⟨a, rfl⟩ := hK.surjective z
    exact ⟨σ a, (RingHom.congr_fun hστ a).symm⟩
  let e := RingEquiv.ofBijective (algebraMap K L) hK
  let e' := RingEquiv.ofBijective (algebraMap K' L') hK'
  have hcomp : σ.toRingHom.comp e.symm.toRingHom = e'.symm.toRingHom.comp τ.toRingHom := by
    apply RingHom.ext
    intro y
    apply e'.injective
    change algebraMap K' L' (σ (e.symm y)) = e' (e'.symm (τ y))
    rw [e'.apply_symm_apply]
    exact (RingHom.congr_fun hστ (e.symm y)).symm.trans (congrArg τ (e.apply_symm_apply y))
  rw [milnorKNormRing_of_bijective hK, milnorKNormRing_of_bijective hK']
  change milnorKRingMapLift σ.toRingHom (milnorKRingMap e.symm.toRingHom x) =
    milnorKRingMap e'.symm.toRingHom (milnorKRingMapLift τ.toRingHom x)
  rw [← milnorKRingMapLift_eq e.symm.toRingHom, ← milnorKRingMapLift_eq e'.symm.toRingHom,
    milnorKRingMapLift_comp_apply, milnorKRingMapLift_comp_apply, hcomp]

/-- The native finite chosen norms commute with compatible simultaneous field equivalences. -/
theorem milnorKNormRing_map_ringEquiv_across_of_finite :
    ∀ {K L : Type u} {K' L' : Type v} [Field K] [Field L] [Field K'] [Field L']
      [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
      (σ : K ≃+* K') (τ : L ≃+* L'),
      τ.toRingHom.comp (algebraMap K L) = (algebraMap K' L').comp σ.toRingHom →
      ∀ x : MilnorKRing L,
        milnorKRingMapLift σ.toRingHom (milnorKNormRing K L x) =
          milnorKNormRing K' L' (milnorKRingMapLift τ.toRingHom x) := by
  classical
  suffices h : ∀ d : ℕ, ∀ (K L : Type u) (K' L' : Type v)
      [Field K] [Field L] [Field K'] [Field L']
      [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L'],
      finrank K L = d →
      ∀ (σ : K ≃+* K') (τ : L ≃+* L'),
      τ.toRingHom.comp (algebraMap K L) = (algebraMap K' L').comp σ.toRingHom →
      ∀ x : MilnorKRing L,
        milnorKRingMapLift σ.toRingHom (milnorKNormRing K L x) =
          milnorKNormRing K' L' (milnorKRingMapLift τ.toRingHom x) by
    intro K L K' L' _ _ _ _ _ _ _ _
    exact h (finrank K L) K L K' L' rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro K L K' L' _ _ _ _ _ _ _ _ hd σ τ hστ x
    by_cases h : ∃ a : L, a ∉ Set.range (algebraMap K L)
    · let a := h.choose
      have hlt : finrank K⟮a⟯ L < d := hd ▸ finrank_adjoin_simple_lt h.choose_spec
      obtain ⟨e, _, heτ, he⟩ := exists_adjoinSimple_ringEquiv_across σ τ hστ
        (Algebra.IsIntegral.isIntegral (R := K) a)
        (Algebra.IsIntegral.isIntegral (R := K') (τ a))
      have hrec := ih _ hlt K⟮a⟯ L K'⟮τ a⟯ L' rfl e τ heτ x
      calc
        _ = milnorKRingMapLift σ.toRingHom (milnorKNormAdjoinSimple K
            (Algebra.IsIntegral.isIntegral a) (milnorKNormRing K⟮a⟯ L x)) :=
          congrArg (milnorKRingMapLift σ.toRingHom) (milnorKNormRing_selected_step_apply h x)
        _ = milnorKNormAdjoinSimple K' (Algebra.IsIntegral.isIntegral (τ a))
            (milnorKRingMapLift e.toRingHom (milnorKNormRing K⟮a⟯ L x)) :=
          he (milnorKNormRing K⟮a⟯ L x)
        _ = milnorKNormAdjoinSimple K' (Algebra.IsIntegral.isIntegral (τ a))
            (milnorKNormRing K'⟮τ a⟯ L' (milnorKRingMapLift τ.toRingHom x)) :=
          congrArg (milnorKNormAdjoinSimple K' (Algebra.IsIntegral.isIntegral (τ a))) hrec
        _ = _ := (milnorKNormRing_eq_adjoinSimple_step_of_finite K' L' (τ a)
          (milnorKRingMapLift τ.toRingHom x)).symm
    · exact norm_equivariance_of_bijective σ τ hστ (bijective_algebraMap_of_forall h) x

end Stacks.Chow

end
