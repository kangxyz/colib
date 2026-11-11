/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.IntermediateField.CompositumImage
public import Colib.FieldTheory.PurelyInseparable.SeparableClosureCompositum
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerNormalPrimePower
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeSeparablePureSquare
public import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleSeparableClosureFactorization

/-!
# Transitivity of the native Milnor norm in finite towers

A mixed compositum rectangle reduces to a prime purely inseparable step.
Factor the norm through the actual maximal separable subfield. The
separable and purely inseparable tower identities then compose the
factorized maps. The native simple Frobenius factorization and the
literal selected recursion identify them with the original norms.
-/

@[expose] public noncomputable section

open IntermediateField Module
open scoped separableClosure

universe u

namespace Stacks.Chow

private theorem adjoin_range_eq_top_swap {A B D : Type u}
    [Field A] [Field B] [Field D] [Algebra A D] [Algebra B D]
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap B D)) = ⊤) :
    IntermediateField.adjoin B (Set.range (algebraMap A D)) = ⊤ := by
  apply IntermediateField.toSubfield_injective
  have h := congrArg (fun S : IntermediateField A D => S.toSubfield) hgen
  rw [adjoin_toSubfield] at h ⊢
  change Subfield.closure
    (Set.range (algebraMap A D) ∪ Set.range (algebraMap B D)) = ⊤ at h
  change Subfield.closure
    (Set.range (algebraMap B D) ∪ Set.range (algebraMap A D)) = ⊤
  rwa [Set.union_comm]

section Generation

variable {K A B D : Type u} [Field K] [Field A] [Field B] [Field D]
  [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
  [IsScalarTower K A D] [IsScalarTower K B D]

private theorem isPurelyInseparable_of_adjoin_range_eq_top [IsPurelyInseparable K B]
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap B D)) = ⊤) :
    IsPurelyInseparable A D := by
  obtain ⟨p, _⟩ := ExpChar.exists K
  let : ExpChar A p := expChar_of_injective_algebraMap (algebraMap K A).injective p
  have hle : IntermediateField.adjoin A (Set.range (algebraMap B D)) ≤ perfectClosure A D := by
    apply adjoin_le_iff.mpr
    rintro _ ⟨b, rfl⟩
    obtain ⟨r, c, hc⟩ := IsPurelyInseparable.pow_mem K p b
    refine (mem_perfectClosure_iff_pow_mem p).mpr ⟨r, algebraMap K A c, ?_⟩
    rw [← IsScalarTower.algebraMap_apply K A D, IsScalarTower.algebraMap_apply K B D, hc, map_pow]
  rw [hgen] at hle
  exact isPurelyInseparable_iff_perfectClosure_eq_top.mpr (top_unique hle)

private theorem isSeparable_of_adjoin_range_eq_top [Algebra.IsSeparable K B]
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap B D)) = ⊤) :
    Algebra.IsSeparable A D := by
  have hle : IntermediateField.adjoin A (Set.range (algebraMap B D)) ≤ separableClosure A D := by
    apply adjoin_le_iff.mpr
    rintro _ ⟨b, rfl⟩
    let f := IsScalarTower.toAlgHom K B D
    exact mem_separableClosure_iff.mpr
      ((IsSeparable.map f f.injective (Algebra.IsSeparable.isSeparable K b)).tower_top A)
  rw [hgen] at hle
  exact ⟨fun z => mem_separableClosure_iff.mp (hle IntermediateField.mem_top)⟩

private theorem bijective_of_adjoin_range_eq_top
    (hB : Function.Bijective (algebraMap K B))
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap B D)) = ⊤) :
    Function.Bijective (algebraMap A D) := by
  refine ⟨(algebraMap A D).injective, fun z => ?_⟩
  have hle : IntermediateField.adjoin A (Set.range (algebraMap B D)) ≤ ⊥ := by
    apply adjoin_le_iff.mpr
    rintro _ ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := hB.surjective b
    rw [← IsScalarTower.algebraMap_apply K B D, IsScalarTower.algebraMap_apply K A D]
    exact (⊥ : IntermediateField A D).algebraMap_mem _
  rw [hgen] at hle
  exact IntermediateField.mem_bot.mp (hle (IntermediateField.mem_top (x := z)))

end Generation

private theorem mixedSquare :
    ∀ (K A B D : Type u) [Field K] [Field A] [Field B] [Field D]
      [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
      [IsScalarTower K A D] [IsScalarTower K B D]
      [FiniteDimensional K A] [FiniteDimensional K B] [FiniteDimensional K D]
      [FiniteDimensional A D] [FiniteDimensional B D]
      [Algebra.IsSeparable K A] [IsPurelyInseparable K B],
      IntermediateField.adjoin A (Set.range (algebraMap B D)) = ⊤ →
      ∀ x : MilnorKRing D,
        milnorKNormRing K B (milnorKNormRing B D x) =
          milnorKNormRing K A (milnorKNormRing A D x) := by
  classical
  suffices step : ∀ n : ℕ, ∀ (K A B D : Type u) [Field K] [Field A] [Field B] [Field D]
      [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
      [IsScalarTower K A D] [IsScalarTower K B D]
      [FiniteDimensional K A] [FiniteDimensional K B] [FiniteDimensional K D]
      [FiniteDimensional A D] [FiniteDimensional B D]
      [Algebra.IsSeparable K A] [IsPurelyInseparable K B],
      finrank K B = n → IntermediateField.adjoin A (Set.range (algebraMap B D)) = ⊤ →
      ∀ x : MilnorKRing D,
        milnorKNormRing K B (milnorKNormRing B D x) =
          milnorKNormRing K A (milnorKNormRing A D x) by
    intro K A B D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact step (finrank K B) K A B D rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K A B D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd hgen x
    by_cases h1 : finrank K B = 1
    · have hbij := bijective_of_adjoin_range_eq_top
        (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1) hgen
      let : Algebra.IsSeparable A D := ⟨fun z => by
        obtain ⟨a, rfl⟩ := hbij.surjective z
        exact isSeparable_algebraMap a⟩
      let : Algebra.IsSeparable K D := Algebra.IsSeparable.trans K A D
      exact (milnorKNormRing_tower_of_isSeparable (M := B) x).trans
        (milnorKNormRing_tower_of_isSeparable (M := A) x).symm
    · obtain ⟨p, _⟩ := ExpChar.exists K
      obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow K B p
      have hp : p.Prime := (expChar_is_prime_or_one K p).resolve_right fun he =>
        h1 (hr.trans (by rw [he, one_pow]))
      let : Fact p.Prime := ⟨hp⟩
      let : CharP K p := (expChar_prime_iff K hp).mp inferInstance
      have hpos : 1 < finrank K B :=
        lt_of_le_of_ne (Nat.succ_le_of_lt finrank_pos) (Ne.symm h1)
      obtain ⟨P, _, hP⟩ := IntermediateField.exists_normal_prime_subfield_of_finrank_pow_embedding
        p r hr (AlgHom.id K B) hpos
      let : IsPurelyInseparable K P := IsPurelyInseparable.tower_bot K P B
      let : IsPurelyInseparable P B := IsPurelyInseparable.tower_top K P B
      let C := IntermediateField.adjoin A (Set.range (algebraMap P D))
      let : Algebra P C := (adjoinRangeFactor P A D).toAlgebra
      let : IsScalarTower P C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let : IsScalarTower K P C := IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap C D).injective (IsScalarTower.algebraMap_apply K P D a)
      let : FiniteDimensional A C := finiteDimensional_adjoin_range_of_finiteDimensional K P A D
      let : FiniteDimensional K C := Module.Finite.trans A C
      let : FiniteDimensional P C := FiniteDimensional.right K P C
      let : FiniteDimensional P D := FiniteDimensional.right K P D
      let : FiniteDimensional P B := FiniteDimensional.right K P B
      let : FiniteDimensional C D := FiniteDimensional.right A C D
      have hgenC : IntermediateField.adjoin A (Set.range (algebraMap P C)) = ⊤ :=
        adjoin_range_adjoinRangeFactor_eq_top P A D
      let : Algebra.IsSeparable P C :=
        isSeparable_of_adjoin_range_eq_top (K := K) (adjoin_range_eq_top_swap hgenC)
      let : IsPurelyInseparable A D :=
        isPurelyInseparable_of_adjoin_range_eq_top (K := K) hgen
      have hgenD : IntermediateField.adjoin C (Set.range (algebraMap B D)) = ⊤ := by
        let S := IntermediateField.adjoin C (Set.range (algebraMap B D))
        have hle : IntermediateField.adjoin A (Set.range (algebraMap B D)) ≤ S.restrictScalars A :=
          adjoin_le_iff.mpr (subset_adjoin C _)
        rw [hgen] at hle
        exact (IntermediateField.restrictScalars_eq_top_iff (K := A)).mp (top_unique hle)
      have hlt : finrank P B < n := by
        rw [← hd, ← finrank_mul_finrank K P B, hP]
        exact lt_mul_left finrank_pos hp.one_lt
      have hrec := ih _ hlt P C B D rfl hgenD x
      calc
        _ = milnorKNormRing K P (milnorKNormRing P B (milnorKNormRing B D x)) :=
          (milnorKNormRing_tower_of_isPurelyInseparable (M := P) (milnorKNormRing B D x)).symm
        _ = milnorKNormRing K P (milnorKNormRing P C (milnorKNormRing C D x)) :=
          congrArg (milnorKNormRing K P) hrec
        _ = milnorKNormRing K A (milnorKNormRing A C (milnorKNormRing C D x)) :=
          milnorKNormRing_comp_of_isSeparable_of_isPurelyInseparable_prime
            (hP.symm ▸ hp) hgenC (milnorKNormRing C D x)
        _ = _ := congrArg (milnorKNormRing K A)
          (milnorKNormRing_tower_of_isPurelyInseparable (M := C) x)

private def factorizedNorm (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : MilnorKRing L →+ MilnorKRing K :=
  (milnorKNormRing K (separableClosure K L)).comp
    (milnorKNormRing (separableClosure K L) L)

private theorem factorizedNorm_tower
    (K M L : Type u) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [FiniteDimensional M L] :
    (factorizedNorm K M).comp (factorizedNorm M L) = factorizedNorm K L := by
  let A := separableClosure K M
  let C := separableClosure K L
  let D := separableClosure M L
  let : FiniteDimensional K D := Module.Finite.trans M D
  let : FiniteDimensional A D := FiniteDimensional.right K A D
  apply AddMonoidHom.ext
  intro x
  change milnorKNormRing K A
      (milnorKNormRing A M (milnorKNormRing M D (milnorKNormRing D L x))) =
    milnorKNormRing K C (milnorKNormRing C L x)
  calc
    _ = milnorKNormRing K A
        (milnorKNormRing A C (milnorKNormRing C D (milnorKNormRing D L x))) :=
      congrArg (milnorKNormRing K A)
        (mixedSquare A C M D (separableClosure.adjoin_range_eq_top K M L)
          (milnorKNormRing D L x))
    _ = milnorKNormRing K A (milnorKNormRing A C (milnorKNormRing C L x)) :=
      congrArg (fun y => milnorKNormRing K A (milnorKNormRing A C y))
        (milnorKNormRing_tower_of_isPurelyInseparable (M := D) x)
    _ = _ := milnorKNormRing_tower_of_isSeparable (milnorKNormRing C L x)

private theorem simpleNorm_factorization (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a : L) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral a) = factorizedNorm K K⟮a⟯ :=
  milnorKNormAdjoinSimple_eq_separableClosure_factorization_of_pureTower
    (fun _ M _ => milnorKNormRing_tower_of_isPurelyInseparable (M := M)) K L a

private theorem milnorKNormRing_eq_factorizedNorm :
    ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
      milnorKNormRing K L = factorizedNorm K L := by
  classical
  suffices h : ∀ n : ℕ, ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
      [FiniteDimensional K L], finrank K L = n →
      milnorKNormRing K L = factorizedNorm K L by
    intro K L _ _ _ _
    exact h (finrank K L) K L rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K L _ _ _ _ hn
    by_cases h : ∃ a : L, a ∉ Set.range (algebraMap K L)
    · let a := h.choose
      have hlt : finrank K⟮a⟯ L < n := hn ▸ finrank_adjoin_simple_lt h.choose_spec
      rw [milnorKNormRing_eq_selected_step h,
        simpleNorm_factorization K L a, ih _ hlt K⟮a⟯ L rfl]
      exact factorizedNorm_tower K K⟮a⟯ L
    · have hb := bijective_algebraMap_of_forall h
      let : Algebra.IsSeparable K L := ⟨fun y => by
        obtain ⟨a, rfl⟩ := hb.surjective y
        exact isSeparable_algebraMap a⟩
      exact (milnorKNormRing_comp_milnorKNormRing_of_isSeparable
        (k := K) (M := separableClosure K L) (L := L)).symm

section FiniteTower

variable {K M L : Type u} [Field K] [Field M] [Field L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
  [FiniteDimensional K M] [FiniteDimensional K L] [FiniteDimensional M L]

/-- The original chosen norm maps compose in every finite field tower. -/
theorem milnorKNormRing_comp_milnorKNormRing_of_finite :
    (milnorKNormRing K M).comp (milnorKNormRing M L) = milnorKNormRing K L := by
  simp only [milnorKNormRing_eq_factorizedNorm]
  exact factorizedNorm_tower K M L

/-- The original chosen norm tower identity evaluated on the whole Milnor ring. -/
theorem milnorKNormRing_tower_of_finite (x : MilnorKRing L) :
    milnorKNormRing K M (milnorKNormRing M L x) = milnorKNormRing K L x :=
  DFunLike.congr_fun (milnorKNormRing_comp_milnorKNormRing_of_finite (M := M)) x

/-- The original chosen norms compose in every homogeneous degree. -/
theorem milnorKNorm_tower_of_finite (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm K M n (milnorKNorm M L n x) = milnorKNorm K L n x := by
  apply Subtype.ext
  exact milnorKNormRing_tower_of_finite (x : MilnorKRing L)

/-- The homogeneous tower identity as equality of the original additive maps. -/
theorem milnorKNorm_comp_milnorKNorm_of_finite (n : ℕ) :
    (milnorKNorm K M n).comp (milnorKNorm M L n) = milnorKNorm K L n := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNorm_tower_of_finite n x

end FiniteTower

/-- An arbitrary actual simple intermediate step computes the original chosen norm. -/
theorem milnorKNormRing_eq_adjoinSimple_step_of_finite
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (a : L) (x : MilnorKRing L) :
    milnorKNormRing K L x =
      milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral a)
        (milnorKNormRing K⟮a⟯ L x) := by
  have hs : milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral a) =
      milnorKNormRing K K⟮a⟯ :=
    (simpleNorm_factorization K L a).trans (milnorKNormRing_eq_factorizedNorm K K⟮a⟯).symm
  rw [hs, milnorKNormRing_tower_of_finite]

attribute [colib_tag "COL-1027"]
  milnorKNormRing_comp_milnorKNormRing_of_finite milnorKNormRing_tower_of_finite
  milnorKNorm_tower_of_finite milnorKNormRing_eq_adjoinSimple_step_of_finite

attribute [colib_tag "COL-1027",
  colib_ref "aglib_milnor_norm_52e09db4"
    "Aglib/KTheory/MilnorK/Norm/FiniteExtension/Tower.lean:146-183" "adaptation"
    "The source proves the tower equation in characteristic zero. This proves it for the \
      original Stacks chosen norms in all finite towers."]
  milnorKNorm_comp_milnorKNorm_of_finite

end Stacks.Chow

end
