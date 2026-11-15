/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.CochainMonoidal
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegrees
import Mathlib.Algebra.Homology.Linear

/-! # The signed tensor of degree-wise single complexes -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "B" => convolutionBifunctor F
local notation "c" => ComplexShape.up ℤ
local notation "Ch" => CochainComplex PST ℤ

attribute [local instance] transferCoefficientAbelian

attribute [local instance] convolutionMonoidalCategory convolutionMonoidalPreadditive
  convolutionSymmetricCategory convolutionCochainMonoidalCategory
  convolutionCochainSymmetricCategory cochainTensorHasCoproducts
  convolutionCurriedTensor_additive convolutionTensorLeft_additive
  convolutionTensorLeft_preservesInitial convolutionTensorRight_preservesInitial
  cochainTensorPreservesCoproducts₁₂ cochainTensorPreservesCoproducts₂₃
  cochainTensorPreservesCoproducts₄

-- Normalize the two comparisons on the one nonzero homogeneous summand.
set_option maxHeartbeats 550000 in
-- The cochain tensor is inferred from its native graded support.
set_option synthInstance.maxHeartbeats 100000 in
-- The comparison identifies both original coproduct inclusions in degree `n + n`.
/-- The cochain braiding on two single complexes in degree `n` is the
coefficient swap multiplied by `(-1)^(n*n)` under the original inclusion. -/
theorem convolutionCochainSingle_braiding (P Q₀ : PST) (n : ℤ) :
    let K := (CochainComplex.singleFunctor PST n).obj P
    let L := (CochainComplex.singleFunctor PST n).obj Q₀
    let e := HomologicalComplex.mapBifunctorSingleSingleIso B P Q₀ n n
    let e' := HomologicalComplex.mapBifunctorSingleSingleIso B Q₀ P n n
    (β_ K L).hom ≫ e'.hom =
      (n * n).negOnePow • (e.hom ≫
        (CochainComplex.singleFunctor PST (n + n)).map (β_ P Q₀).hom) := by
  intro K L e e'
  let m := n + n
  let j := HomologicalComplex.ιTensorObj K L n n m rfl
  let U₀ := HomologicalComplex.singleObjXSelf c n P
  let V₀ := HomologicalComplex.singleObjXSelf c n Q₀
  let u := HomologicalComplex.singleObjXSelf c m (P ⊗ Q₀)
  let v := HomologicalComplex.singleObjXSelf c m (Q₀ ⊗ P)
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = m
  · subst i
    let : IsIso j :=
      HomologicalComplex.isIso_ιMapBifunctor_single_single (curriedTensor PST) P Q₀ n n
    apply (cancel_epi j).1
    simp only [HomologicalComplex.comp_f, HomologicalComplex.units_smul_f_apply,
      Linear.comp_units_smul]
    have h₁ : j ≫ (β_ K L).hom.f m = (n * n).negOnePow •
        ((β_ (K.X n) (L.X n)).hom ≫ HomologicalComplex.ιTensorObj L K n n m rfl) :=
      CochainComplex.ιTensorObj_koszulBraiding K L n n m rfl
    have h₂ : j ≫ e.hom.f m = (U₀.hom ⊗ₘ V₀.hom) ≫ u.inv := by
      rw [MonoidalCategory.tensorHom_def, Category.assoc]
      exact HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f (curriedTensor PST) P Q₀ n n
    have h₃ : HomologicalComplex.ιTensorObj L K n n m rfl ≫ e'.hom.f m =
        (V₀.hom ⊗ₘ U₀.hom) ≫ v.inv := by
      rw [MonoidalCategory.tensorHom_def, Category.assoc]
      exact HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f (curriedTensor PST) Q₀ P n n
    let t := (CochainComplex.singleFunctor PST m).map (β_ P Q₀).hom
    have ht : t.f m = u.hom ≫ (β_ P Q₀).hom ≫ v.inv :=
      HomologicalComplex.single_map_f_self _ _ _
    have hβ := (BraidedCategory.braiding_naturality U₀.hom V₀.hom).symm
    have hu : u.inv ≫ t.f m = (β_ P Q₀).hom ≫ v.inv :=
      (congrArg (u.inv ≫ ·) ht).trans (u.inv_hom_id_assoc _)
    change j ≫ (β_ K L).hom.f m ≫ e'.hom.f m =
      (n * n).negOnePow • (j ≫ e.hom.f m ≫ t.f m)
    rw [reassoc_of% h₁, Linear.units_smul_comp, Category.assoc, h₃, reassoc_of% h₂]
    exact congrArg ((n * n).negOnePow • ·)
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ v.inv) hβ)).trans
        ((Category.assoc _ _ _).trans (congrArg ((U₀.hom ⊗ₘ V₀.hom) ≫ ·) hu.symm)))
  · exact (HomologicalComplex.isZero_mapBifunctor_single_single_X B P Q₀ n n i hi).eq_of_src _ _


-- Compute the actual coefficient maps under the two single-complex evaluations.
set_option maxHeartbeats 550000 in
-- The cochain tensor is inferred from its native graded support.
set_option synthInstance.maxHeartbeats 100000 in
-- Coefficient maps are evaluated in the original signed total.
/-- The comparison on two single complexes preserves the actual tensor of coefficient maps. -/
theorem convolutionCochainSingle_naturality {P P' Q₀ Q₀' : PST}
    (f : P ⟶ P') (g : Q₀ ⟶ Q₀')
    (n : ℤ) :
    let s := CochainComplex.singleFunctor PST n
    let s' := CochainComplex.singleFunctor PST (n + n)
    (s.map f ⊗ₘ s.map g) ≫
        (HomologicalComplex.mapBifunctorSingleSingleIso B P' Q₀' n n).hom =
      (HomologicalComplex.mapBifunctorSingleSingleIso B P Q₀ n n).hom ≫
        s'.map (f ⊗ₘ g) := by
  intro s s'
  let m := n + n
  let K := s.obj P
  let L := s.obj Q₀
  let K' := s.obj P'
  let L' := s.obj Q₀'
  let j := HomologicalComplex.ιTensorObj K L n n m rfl
  let j' := HomologicalComplex.ιTensorObj K' L' n n m rfl
  let u (A : PST) := HomologicalComplex.singleObjXSelf c n A
  let v (A : PST) := HomologicalComplex.singleObjXSelf c m A
  let b := HomologicalComplex.mapBifunctorSingleSingleIso B P Q₀ n n
  let b' := HomologicalComplex.mapBifunctorSingleSingleIso B P' Q₀' n n
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = m
  · subst i
    let : IsIso j :=
      HomologicalComplex.isIso_ιMapBifunctor_single_single (curriedTensor PST) P Q₀ n n
    apply (cancel_epi j).1
    have h₁ : j ≫ (s.map f ⊗ₘ s.map g).f m =
        ((s.map f).f n ⊗ₘ (s.map g).f n) ≫ j' := by
      let f₀ := (s.map f).f n
      let g₀ := (s.map g).f n
      have h := HomologicalComplex.ι_mapBifunctorMap (s.map f) (s.map g)
        (curriedTensor PST) c n n m rfl
      change j ≫ (s.map f ⊗ₘ s.map g).f m = (f₀ ▷ L.X n) ≫ (K'.X n ◁ g₀) ≫ j' at h
      exact h.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ j') (MonoidalCategory.tensorHom_def f₀ g₀).symm))
    have h₂ : j ≫ b.hom.f m = ((u P).hom ⊗ₘ (u Q₀).hom) ≫ (v (P ⊗ Q₀)).inv := by
      rw [MonoidalCategory.tensorHom_def, Category.assoc]
      exact HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f (curriedTensor PST) P Q₀ n n
    have h₃ : j' ≫ b'.hom.f m =
        ((u P').hom ⊗ₘ (u Q₀').hom) ≫ (v (P' ⊗ Q₀')).inv := by
      rw [MonoidalCategory.tensorHom_def, Category.assoc]
      exact HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f (curriedTensor PST) P' Q₀' n n
    change j ≫ (s.map f ⊗ₘ s.map g).f m ≫ b'.hom.f m =
      j ≫ b.hom.f m ≫ (s'.map (f ⊗ₘ g)).f m
    let f₀ := (s.map f).f n
    let g₀ := (s.map g).f n
    let t := (s'.map (f ⊗ₘ g)).f m
    have hf : f₀ ≫ (u P').hom = (u P).hom ≫ f := by
      have h : f₀ = (u P).hom ≫ f ≫ (u P').inv :=
        HomologicalComplex.single_map_f_self _ _ _
      exact (congrArg (· ≫ (u P').hom) h).trans (by
        rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hg : g₀ ≫ (u Q₀').hom = (u Q₀).hom ≫ g := by
      have h : g₀ = (u Q₀).hom ≫ g ≫ (u Q₀').inv :=
        HomologicalComplex.single_map_f_self _ _ _
      exact (congrArg (· ≫ (u Q₀').hom) h).trans (by
        rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have ht : t = (v (P ⊗ Q₀)).hom ≫ (f ⊗ₘ g) ≫ (v (P' ⊗ Q₀')).inv :=
      HomologicalComplex.single_map_f_self _ _ _
    calc
      _ = (f₀ ⊗ₘ g₀) ≫ (j' ≫ b'.hom.f m) := (reassoc_of% h₁) (b'.hom.f m)
      _ = (f₀ ⊗ₘ g₀) ≫ (((u P').hom ⊗ₘ (u Q₀').hom) ≫ (v (P' ⊗ Q₀')).inv) :=
        congrArg ((f₀ ⊗ₘ g₀) ≫ ·) h₃
      _ = ((u P).hom ⊗ₘ (u Q₀).hom) ≫
          (f ⊗ₘ g) ≫ (v (P' ⊗ Q₀')).inv := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
          ← tensorHom_comp_tensorHom, Category.assoc]
      _ = ((u P).hom ⊗ₘ (u Q₀).hom) ≫ (v (P ⊗ Q₀)).inv ≫ t := by
        rw [ht, Iso.inv_hom_id_assoc]
      _ = _ := ((reassoc_of% h₂) t).symm
  · exact (HomologicalComplex.isZero_mapBifunctor_single_single_X B P Q₀ n n i hi).eq_of_src _ _


end AlgebraicGeometry.PresheafWithTransfers
