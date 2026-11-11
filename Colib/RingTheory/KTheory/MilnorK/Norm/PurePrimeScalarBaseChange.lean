/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeInseparableChosenComparison
import Colib.FieldTheory.Polynomial.CoprimeDegree
import Colib.RingTheory.KTheory.MilnorK.Norm.ScalarFactorBaseChange

/-!
# Scalar base change preserving a purely inseparable prime presentation

The actual generator and its irreducible coefficient image give the two
polynomial presentations. The weighted factor formula is a singleton with
multiplicity one.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {K E B D : Type u} [Field K] [Field E] [Field B] [Field D]
  [Algebra K E] [Algebra K B] [Algebra K D] [Algebra E D] [Algebra B D]
  [IsScalarTower K E D] [IsScalarTower K B D]
  [FiniteDimensional K E] [FiniteDimensional B D]
  [IsPurelyInseparable K E] [IsPurelyInseparable B D]

/-- Restriction under a coefficient map preserving the given prime presentation
commutes with the original chosen norms. -/
theorem milnorKNormRing_baseChange_of_prime_of_isPurelyInseparable_of_irreducible_map
    (hp : Nat.Prime (finrank K E)) (a : E) (ha : a ∉ Set.range (algebraMap K E))
    (hpreserve : Irreducible ((minpoly K a).map (algebraMap K B)))
    (hdegree : finrank B D = finrank K E) (x : MilnorKRing E) :
    milnorKRingMap (algebraMap K B) (milnorKNormRing K E x) =
      milnorKNormRing B D (milnorKRingMap (algebraMap E D) x) := by
  classical
  let b := algebraMap E D a
  have haInt : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  have hbInt : IsIntegral B b := Algebra.IsIntegral.isIntegral b
  let p := minpolyOfDegree K haInt
  let q := minpolyOfDegree B hbInt
  let f : K⟮a⟯ ≃ₐ[K] E := AlgEquiv.ofBijective (IntermediateField.val K⟮a⟯)
    (bijective_algebraMap_adjoin_simple_of_finrank_prime hp ha)
  have hpDegree : (poly p).natDegree = finrank K E :=
    (IntermediateField.adjoin.finrank haInt).symm.trans f.toLinearEquiv.finrank_eq
  have hdiv : poly q ∣ (poly p).map (algebraMap K B) :=
    minpoly.dvd_map_of_isScalarTower' K B D a
  have hirr : Irreducible ((poly p).map (algebraMap K B)) := hpreserve
  have hmap : (poly p).map (algebraMap K B) = poly q :=
    Polynomial.eq_of_monic_of_associated ((monic p).map _) (monic q)
      ((irreducible q).associated_of_dvd hirr hdiv).symm
  have hqDegree : (minpoly B b).natDegree = finrank K E := by
    change (poly q).natDegree = finrank K E
    rw [← hmap, Polynomial.natDegree_map, hpDegree]
  have hb : b ∉ Set.range (algebraMap B D) := fun h =>
    hp.ne_one (hqDegree.symm.trans (minpoly.natDegree_eq_one_iff.mpr h))
  have hp' : Nat.Prime (finrank B D) := by rwa [hdegree]
  let g : B⟮b⟯ ≃ₐ[B] D := AlgEquiv.ofBijective (IntermediateField.val B⟮b⟯)
    (bijective_algebraMap_adjoin_simple_of_finrank_prime hp' hb)
  let e : (K[X] ⧸ Ideal.span {poly p}) ≃ₐ[K] E := (adjoinRootEquivAdjoin K haInt).trans f
  let e' : (B[X] ⧸ Ideal.span {poly q}) ≃ₐ[B] D := (adjoinRootEquivAdjoin B hbInt).trans g
  have he : e (AdjoinRoot.root (poly p)) = a := by
    change f (adjoinRootEquivAdjoin K haInt (AdjoinRoot.root (minpoly K a))) = a
    rw [adjoinRootEquivAdjoin_apply_root]
    rfl
  have he' : e' (AdjoinRoot.root (poly q)) = b := by
    change g (adjoinRootEquivAdjoin B hbInt (AdjoinRoot.root (minpoly B b))) = b
    rw [adjoinRootEquivAdjoin_apply_root]
    rfl
  let j : (K[X] ⧸ Ideal.span {poly p}) →+* (B[X] ⧸ Ideal.span {poly q}) :=
    AdjoinRoot.map (algebraMap K B) (poly p) (poly q) hdiv
  have hquot : e'.toRingHom.comp j = (algebraMap E D).comp e.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      change e' (AdjoinRoot.map (algebraMap K B) (poly p) (poly q) hdiv
        (AdjoinRoot.of (poly p) c)) = algebraMap E D (e (AdjoinRoot.of (poly p) c))
      rw [AdjoinRoot.map_of]
      change e' (algebraMap B (B[X] ⧸ Ideal.span {poly q}) (algebraMap K B c)) =
        algebraMap E D (e (algebraMap K (K[X] ⧸ Ideal.span {poly p}) c))
      rw [e'.commutes, e.commutes, ← IsScalarTower.algebraMap_apply K B D,
        ← IsScalarTower.algebraMap_apply K E D]
    · change e' (AdjoinRoot.map (algebraMap K B) (poly p) (poly q) hdiv
        (AdjoinRoot.root (poly p))) = algebraMap E D (e (AdjoinRoot.root (poly p)))
      rw [AdjoinRoot.map_root, he', he]
  have hcomp : j.comp e.symm.toRingHom = e'.symm.toRingHom.comp (algebraMap E D) := by
    apply RingHom.ext
    intro z
    apply e'.injective
    change e' (j (e.symm z)) = e' (e'.symm (algebraMap E D z))
    rw [e'.apply_symm_apply]
    change (e'.toRingHom.comp j) (e.symm z) = algebraMap E D z
    rw [hquot]
    change algebraMap E D (e (e.symm z)) = algebraMap E D z
    rw [e.apply_symm_apply]
  have hcover : ∀ (d : ℕ) (r : MonicIrreducibleOfDegree B d),
      poly r ∣ (poly p).map (algebraMap K B) →
        ∃ i ∈ ({PUnit.unit} : Finset PUnit.{1}), poly r = poly q := by
    intro d r hr
    refine ⟨PUnit.unit, Finset.mem_singleton_self _, ?_⟩
    rw [hmap] at hr
    exact Polynomial.eq_of_monic_of_associated (monic r) (monic q)
      ((irreducible r).associated_of_dvd (irreducible q) hr)
  have hmult : multiplicity (poly q) ((poly p).map (algebraMap K B)) = 1 := by
    rw [hmap]
    exact (irreducible q).multiplicity_self
  have hfactor : milnorKRingMap (algebraMap K B)
      (simpleMilnorNorm p (milnorKRingMap e.symm.toRingHom x)) =
        simpleMilnorNorm q (milnorKRingMap j (milnorKRingMap e.symm.toRingHom x)) := by
    have h := simpleMilnorNorm_map_eq_weighted_sum_of_factors
      (algebraMap K B) p (milnorKRingMap e.symm.toRingHom x)
      ({PUnit.unit} : Finset PUnit.{1}) (fun _ => (minpoly B b).natDegree) (fun _ => q)
      (fun i _ k _ _ => Subsingleton.elim i k) (fun _ => hdiv) hcover
    simpa only [Finset.sum_singleton, hmult, Nat.cast_one, one_zsmul] using h
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
      hp p e.symm x,
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
      hp' q e'.symm (milnorKRingMap (algebraMap E D) x),
    hfactor, milnorKRingMap_comp_apply, hcomp, ← milnorKRingMap_comp_apply]

/-- The base-change square on each original homogeneous group. -/
theorem milnorKNorm_baseChange_of_prime_of_isPurelyInseparable_of_irreducible_map
    (hp : Nat.Prime (finrank K E)) (a : E) (ha : a ∉ Set.range (algebraMap K E))
    (hpreserve : Irreducible ((minpoly K a).map (algebraMap K B)))
    (hdegree : finrank B D = finrank K E) (n : ℕ) (x : MilnorKTheory E n) :
    milnorKTheoryMap (algebraMap K B) n (milnorKNorm K E n x) =
      milnorKNorm B D n (milnorKTheoryMap (algebraMap E D) n x) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_baseChange_of_prime_of_isPurelyInseparable_of_irreducible_map
    hp a ha hpreserve hdegree (x : MilnorKRing E)

end Stacks.Chow

end
