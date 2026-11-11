/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PureBaseChangeSimple
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerSeparable
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Chosen Milnor norms after purely inseparable scalar extension

Suppose a purely inseparable extension of the coefficient field makes the
compositum separable. Restricting the original chosen norm then gives the norm
of the compositum with the original inseparable degree as its coefficient.
The proof follows the selected recursion and applies the weighted simple
norm formula at each step.
-/

@[expose] public noncomputable section

open IntermediateField Module

universe u

namespace Stacks.Chow

variable {K B L D : Type u} [Field K] [Field B] [Field L] [Field D]
  [Algebra K B] [Algebra K L] [Algebra K D] [Algebra B D] [Algebra L D]
  [IsScalarTower K B D] [IsScalarTower K L D]

private theorem isPurelyInseparable_adjoinSimpleBaseChange
    [IsPurelyInseparable K B] (a : L) :
    let f := IsScalarTower.toAlgHom K L D
    let _ : Algebra K⟮a⟯ B⟮f a⟯ := (adjoinSimpleBaseChangeMap (K' := B) f a).toAlgebra
    IsPurelyInseparable K⟮a⟯ B⟮f a⟯ := by
  dsimp only
  let f := IsScalarTower.toAlgHom K L D
  let E := K⟮a⟯
  let C := B⟮f a⟯
  let : Algebra E C := (adjoinSimpleBaseChangeMap (K' := B) f a).toAlgebra
  let : IsScalarTower E C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨p, _⟩ := ExpChar.exists K
  let : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  let P := perfectClosure E D
  have hB (b : B) : algebraMap B D b ∈ P := by
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K p b
    refine (mem_perfectClosure_iff_pow_mem p).2 ⟨n, algebraMap K E c, ?_⟩
    rw [← IsScalarTower.algebraMap_apply K E D, IsScalarTower.algebraMap_apply K B D,
      hc, map_pow]
  have hC : C ≤ P.toSubfield.toIntermediateField hB := by
    apply IntermediateField.adjoin_simple_le_iff.mpr
    change f a ∈ perfectClosure E D
    refine (mem_perfectClosure_iff_pow_mem p).2 ⟨0, AdjoinSimple.gen K a, ?_⟩
    rw [pow_zero, pow_one]
    rfl
  change IsPurelyInseparable E C
  apply (isPurelyInseparable_iff_pow_mem E p).2
  intro x
  have hx : (x : D) ∈ perfectClosure E D := hC x.property
  obtain ⟨n, e, he⟩ := (mem_perfectClosure_iff_pow_mem p).1 hx
  refine ⟨n, e, (algebraMap C D).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply E C D, map_pow]
  exact he

private theorem chosen_baseChange_of_bijective
    [FiniteDimensional K L] [FiniteDimensional B D]
    (h : Function.Bijective (algebraMap K L))
    (hgen : IntermediateField.adjoin B (Set.range (algebraMap L D)) = ⊤)
    (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K B) (milnorKNormRing K L x) =
      (Field.finInsepDegree K L : ℤ) •
        milnorKNormRing B D (milnorKRingMap (algebraMap L D) x) := by
  have hBD : Function.Bijective (algebraMap B D) := by
    refine ⟨(algebraMap B D).injective, fun y => ?_⟩
    have hrange : Set.range (algebraMap L D) ⊆ (⊥ : IntermediateField B D) := by
      rintro _ ⟨l, rfl⟩
      obtain ⟨k, rfl⟩ := h.surjective l
      rw [← IsScalarTower.algebraMap_apply K L D, IsScalarTower.algebraMap_apply K B D]
      exact (⊥ : IntermediateField B D).algebraMap_mem _
    have hbot : (⊤ : IntermediateField B D) ≤ ⊥ := hgen ▸ adjoin_le_iff.mpr hrange
    exact IntermediateField.mem_bot.mp
      (hbot (IntermediateField.mem_top : y ∈ (⊤ : IntermediateField B D)))
  let e := RingEquiv.ofBijective (algebraMap K L) h
  let e' := RingEquiv.ofBijective (algebraMap B D) hBD
  have hmap : (algebraMap K B).comp e.symm.toRingHom =
      e'.symm.toRingHom.comp (algebraMap L D) := by
    ext l
    apply e'.injective
    change algebraMap B D (algebraMap K B (e.symm l)) = e' (e'.symm (algebraMap L D l))
    rw [e'.apply_symm_apply, ← IsScalarTower.algebraMap_apply K B D,
      IsScalarTower.algebraMap_apply K L D]
    exact congrArg (algebraMap L D) (e.apply_symm_apply l)
  have hdeg : finrank K L = 1 := Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr h
  have hsepInsep := Field.finSepDegree_mul_finInsepDegree K L
  rw [hdeg] at hsepInsep
  have hi : Field.finInsepDegree K L = 1 := Nat.dvd_one.mp
    ⟨Field.finSepDegree K L, by simpa only [Nat.mul_comm] using hsepInsep.symm⟩
  rw [milnorKNormRing_of_bijective h, milnorKNormRing_of_bijective hBD, hi,
    Nat.cast_one, one_zsmul, milnorKRingMap_comp_apply, milnorKRingMap_comp_apply]
  exact congrArg (fun g : L →+* B => milnorKRingMap g x) hmap

private theorem chosen_baseChange_of_isPurelyInseparable_aux :
    ∀ (n : ℕ) (K B L D : Type u) [Field K] [Field B] [Field L] [Field D]
      [Algebra K B] [Algebra K L] [Algebra K D] [Algebra B D] [Algebra L D]
      [IsScalarTower K B D] [IsScalarTower K L D] [FiniteDimensional K L]
      [FiniteDimensional B D] [IsPurelyInseparable K B] [Algebra.IsSeparable B D],
      finrank K L = n → IntermediateField.adjoin B (Set.range (algebraMap L D)) = ⊤ →
      ∀ x : MilnorKRing L,
        milnorKRingMap (algebraMap K B) (milnorKNormRing K L x) =
          (Field.finInsepDegree K L : ℤ) •
            milnorKNormRing B D (milnorKRingMap (algebraMap L D) x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K B L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn hgen x
    classical
    by_cases h : ∃ a : L, a ∉ Set.range (algebraMap K L)
    · let a := h.choose
      let f := IsScalarTower.toAlgHom K L D
      let E := K⟮a⟯
      let C := B⟮f a⟯
      let i := adjoinSimpleBaseChangeMap (K' := B) f a
      let : Algebra E C := i.toAlgebra
      let : IsScalarTower E C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let : IsPurelyInseparable E C := isPurelyInseparable_adjoinSimpleBaseChange a
      let : FiniteDimensional C D := FiniteDimensional.right B C D
      let : Algebra.IsSeparable C D := Algebra.isSeparable_tower_top_of_isSeparable B C D
      let : Algebra.IsSeparable B C := Algebra.isSeparable_tower_bot_of_isSeparable B C D
      have hgenC : IntermediateField.adjoin C (Set.range (algebraMap L D)) = ⊤ := by
        let S := IntermediateField.adjoin C (Set.range (algebraMap L D))
        have hle : IntermediateField.adjoin B (Set.range (algebraMap L D)) ≤
            S.restrictScalars B := adjoin_le_iff.mpr
          (IntermediateField.subset_adjoin C (Set.range (algebraMap L D)))
        rw [hgen] at hle
        exact (IntermediateField.restrictScalars_eq_top_iff (K := B)).mp (top_unique hle)
      have hrec := ih (finrank E L) (hn ▸ finrank_adjoin_simple_lt h.choose_spec)
        E C L D rfl hgenC x
      have ha : IsIntegral K a := Algebra.IsIntegral.isIntegral a
      have ha' : IsIntegral B (f a) := (IsIntegral.map f ha).tower_top
      have hsimple (z : MilnorKRing C) :
          milnorKNormAdjoinSimple B ha' z = milnorKNormRing B C z := by
        symm
        exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable
          (minpolyOfDegree B ha') (adjoinSimpleEquivQuot B ha') z
      have hsep : IsSeparable B (f a) := Algebra.IsSeparable.isSeparable B (f a)
      rw [milnorKNormRing_selected_step_apply h,
        milnorKNormAdjoinSimple_baseChange_of_isPurelyInseparable f ha hsep,
        hsimple]
      change (Field.finInsepDegree K E : ℤ) •
        milnorKNormRing B C (milnorKRingMap (algebraMap E C) (milnorKNormRing E L x)) = _
      rw [hrec, map_zsmul, smul_smul, ← Nat.cast_mul,
        Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K E L,
        milnorKNormRing_tower_of_isSeparable]
    · exact chosen_baseChange_of_bijective (bijective_algebraMap_of_forall h) hgen x

/-- If a purely inseparable coefficient extension makes the actual compositum
separable, its norm computes the restriction of the original chosen norm
with the original inseparable degree as multiplicity. -/
theorem milnorKNormRing_baseChange_of_isPurelyInseparable
    [FiniteDimensional K L] [FiniteDimensional B D]
    [IsPurelyInseparable K B] [Algebra.IsSeparable B D]
    (hgen : IntermediateField.adjoin B (Set.range (algebraMap L D)) = ⊤)
    (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K B) (milnorKNormRing K L x) =
      (Field.finInsepDegree K L : ℤ) •
        milnorKNormRing B D (milnorKRingMap (algebraMap L D) x) :=
  chosen_baseChange_of_isPurelyInseparable_aux (finrank K L) K B L D rfl hgen x

end Stacks.Chow

end
