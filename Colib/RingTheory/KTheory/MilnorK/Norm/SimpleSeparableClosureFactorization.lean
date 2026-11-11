/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleFrobeniusFactorization
public import Mathlib.FieldTheory.SeparableClosure

import Colib.FieldTheory.AdjoinRoot.Separable
import Colib.FieldTheory.PurelyInseparable.SeparableClosureCompositum
import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerSeparable

/-!
# Factorization of the simple Milnor norm through the separable closure

An inseparable minimal polynomial contracts to a polynomial of smaller degree.
The native power-substitution comparison supplies each step. Transitivity for
purely inseparable extensions combines the steps through the actual maximal
separable subfield.
-/

@[expose] public noncomputable section

open IntermediateField Module Polynomial
open scoped separableClosure

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

private abbrev PureTower : Prop :=
  ∀ (K M L : Type u) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [FiniteDimensional M L]
    [IsPurelyInseparable K L] (x : MilnorKRing L),
      milnorKNormRing K M (milnorKNormRing M L x) = milnorKNormRing K L x

private theorem norm_separableClosure_comp_pure
    (pureTower : PureTower.{u}) (K M L : Type u) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [FiniteDimensional M L]
    [IsPurelyInseparable M L] (x : MilnorKRing L) :
    milnorKNormRing K (separableClosure K M)
      (milnorKNormRing (separableClosure K M) M (milnorKNormRing M L x)) =
    milnorKNormRing K (separableClosure K L) (milnorKNormRing (separableClosure K L) L x) := by
  let C := separableClosure K M
  let D := separableClosure K L
  let : IsScalarTower C D L := IsScalarTower.of_algebraMap_eq fun a =>
    (separableClosure.coe_towerMap_apply K M L a).symm
  let : FiniteDimensional C L := FiniteDimensional.right K C L
  let : IsPurelyInseparable C L := IsPurelyInseparable.trans C M L
  calc
    _ = milnorKNormRing K C (milnorKNormRing C L x) :=
      congrArg (milnorKNormRing K C) (pureTower C M L x)
    _ = milnorKNormRing K C (milnorKNormRing C D (milnorKNormRing D L x)) :=
      congrArg (milnorKNormRing K C) (pureTower C D L x).symm
    _ = _ := milnorKNormRing_tower_of_isSeparable (milnorKNormRing D L x)

variable {k : Type u} [Field k] {p d e : ℕ}

local notation "Q" φ => Polynomial k ⧸ Ideal.span {poly φ}

private theorem isPurelyInseparable_frobeniusParameterResidueMap [ExpChar k p]
    (φ : MonicIrreducibleOfDegree k d) (ψ : MonicIrreducibleOfDegree k e)
    (h : poly ψ ∣ expand k p (poly φ)) :
    letI := (frobeniusParameterResidueMap φ ψ h).toRingHom.toAlgebra
    IsPurelyInseparable (Q φ) (Q ψ) := by
  let := (frobeniusParameterResidueMap φ ψ h).toRingHom.toAlgebra
  let : ExpChar (Q φ) p := expChar_of_injective_algebraMap (algebraMap k (Q φ)).injective p
  apply (isPurelyInseparable_iff_pow_mem (Q φ) p).mpr
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨1, Ideal.Quotient.mk _ (f.map (frobenius k p)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {poly ψ}) (expand k p (f.map (frobenius k p))) =
    (Ideal.Quotient.mk (Ideal.span {poly ψ}) f) ^ (p ^ 1)
  rw [expand_map_frobenius, map_pow, pow_one]

private theorem simpleMilnorNorm_eq_separableClosure_factorization
    (pureTower : PureTower.{u}) (ψ : MonicIrreducibleOfDegree k d) (x : MilnorKRing (Q ψ)) :
    letI : Module.Finite k (Q ψ) := (monic ψ).finite_adjoinRoot
    simpleMilnorNorm ψ x =
      milnorKNormRing k (separableClosure k (Q ψ))
        (milnorKNormRing (separableClosure k (Q ψ)) (Q ψ) x) := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  induction d using Nat.strong_induction_on with
  | h d ih =>
    let : Module.Finite k (Q ψ) := (monic ψ).finite_adjoinRoot
    by_cases hsep : (poly ψ).Separable
    · let : Fact (Irreducible (poly ψ)) := ⟨irreducible ψ⟩
      let : Algebra.IsSeparable k (Q ψ) :=
        AdjoinRoot.isSeparable_of_polynomial_separable _ hsep
      let ε : (Q ψ) ≃ₐ[k] AdjoinRoot (poly ψ) :=
        { toRingEquiv := RingEquiv.refl _, commutes' := fun _ => rfl }
      have hsimple := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable ψ ε x
      change milnorKNormRing k (Q ψ) x =
        simpleMilnorNorm ψ (milnorKRingMap (RingHom.id (Q ψ)) x) at hsimple
      rw [milnorKRingMap_id_apply] at hsimple
      exact hsimple.symm.trans
        (milnorKNormRing_tower_of_isSeparable (M := separableClosure k (Q ψ)) x).symm
    · have hp : Nat.Prime p := by
        cases ‹ExpChar k p› with
        | zero => exact (hsep (irreducible ψ).separable).elim
        | prime hp => exact hp
      have hderiv : derivative (poly ψ) = 0 := by
        by_contra hne
        exact hsep ((separable_iff_derivative_ne_zero (irreducible ψ)).mpr hne)
      let f := contract p (poly ψ)
      have hf : expand k p f = poly ψ := expand_contract' p hderiv
      have hmonic : f.Monic := (monic_expand_iff hp.pos).mp (hf.symm ▸ monic ψ)
      have hirr : Irreducible f := of_irreducible_expand hp.ne_zero (hf.symm ▸ irreducible ψ)
      let φ : MonicIrreducibleOfDegree k f.natDegree := ⟨f, hmonic, hirr, rfl⟩
      have hdiv : poly ψ ∣ expand k p (poly φ) := hf.symm ▸ dvd_rfl
      have hlt : f.natDegree < d := by
        have hdeg := congrArg natDegree hf
        rw [natDegree_expand, natDegree_eq ψ] at hdeg
        exact hdeg ▸ lt_mul_of_one_lt_right hirr.natDegree_pos hp.one_lt
      let : Algebra (Q φ) (Q ψ) := (frobeniusParameterResidueMap φ ψ hdiv).toRingHom.toAlgebra
      let : IsScalarTower k (Q φ) (Q ψ) :=
        IsScalarTower.of_algebraMap_eq fun a =>
          ((frobeniusParameterResidueMap φ ψ hdiv).commutes a).symm
      let : Module.Finite k (Q φ) := (monic φ).finite_adjoinRoot
      let : FiniteDimensional (Q φ) (Q ψ) := finite_frobeniusParameterResidueMap φ ψ hdiv
      let : IsPurelyInseparable (Q φ) (Q ψ) := isPurelyInseparable_frobeniusParameterResidueMap
        φ ψ hdiv
      rw [simpleMilnorNorm_eq_frobeniusParameter hp φ ψ hdiv x,
        ih f.natDegree hlt φ (milnorKNormRing (Q φ) (Q ψ) x)]
      exact norm_separableClosure_comp_pure pureTower k (Q φ) (Q ψ) x

/-- The native chosen simple step factors through the maximal separable
subfield of the actual adjoined field, given purely inseparable norm transitivity. -/
theorem milnorKNormAdjoinSimple_eq_separableClosure_factorization_of_pureTower
    (pureTower : ∀ (F E D : Type u) [Field F] [Field E] [Field D]
      [Algebra F E] [Algebra F D] [Algebra E D] [IsScalarTower F E D]
      [FiniteDimensional F E] [FiniteDimensional F D] [FiniteDimensional E D]
      [IsPurelyInseparable F D] (x : MilnorKRing D),
        milnorKNormRing F E (milnorKNormRing E D x) = milnorKNormRing F D x)
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (a : L) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a) =
      (milnorKNormRing K (separableClosure K K⟮a⟯)).comp
        (milnorKNormRing (separableClosure K K⟮a⟯) K⟮a⟯) := by
  let ha := Algebra.IsIntegral.isIntegral (R := K) a
  let ψ := minpolyOfDegree K ha
  let A := K⟮a⟯
  let B := Polynomial K ⧸ Ideal.span {poly ψ}
  let f : A ≃ₐ[K] B := adjoinSimpleEquivQuot K ha
  let : Module.Finite K B := (monic ψ).finite_adjoinRoot
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun b => (f.commutes b).symm
  let : FiniteDimensional A B := FiniteDimensional.right K A B
  let : IsPurelyInseparable A B := ⟨inferInstance, fun y _ => f.surjective y⟩
  have hdeg : finrank A B = 1 := Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr f.bijective
  apply AddMonoidHom.ext
  intro x
  let y : MilnorKRing B := milnorKRingMap f.toRingHom x
  have hy : milnorKNormRing A B y = x := by
    change milnorKNormRing A B (milnorKRingMap (algebraMap A B) x) = x
    rw [milnorKNormRing_milnorKRingMap, hdeg, Nat.cast_one, one_zsmul]
  have hfac := norm_separableClosure_comp_pure pureTower K A B y
  rw [hy] at hfac
  change simpleMilnorNorm ψ y =
    milnorKNormRing K (separableClosure K A) (milnorKNormRing (separableClosure K A) A x)
  exact (simpleMilnorNorm_eq_separableClosure_factorization pureTower ψ y).trans hfac.symm

end Stacks.Chow

end
