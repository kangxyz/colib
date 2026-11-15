/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Pretriangulated
public import Colib.CategoryTheory.Triangulated.Stabilization.Idempotents

/-! # Triangulated finite-twist stabilization

The octahedron axiom is a finite diagram. Realize its six objects and its three
input triangles at one common level, take the original octahedron, and transport
its two new arrows back by full faithfulness.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open Pretriangulated Limits ZeroObject Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (T : C ⥤ C) [T.Full] [T.Faithful] [T.CommShift ℤ] [T.IsTriangulated]

set_option backward.isDefEq.respectTransparency false in
instance : IsTriangulated (Stabilization T) where
  octahedron_axiom {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃} {u₁₂ u₂₃ u₁₃} comm
      {v₁₂ w₁₂} h₁₂ {v₂₃ w₂₃} h₂₃ {v₁₃ w₁₃} h₁₃ := by
    let n := X₁.level + X₂.level + X₃.level + Z₁₂.level + Z₂₃.level + Z₁₃.level
    have hX₁ : X₁.level ≤ n := by dsimp [n]; omega
    have hX₂ : X₂.level ≤ n := by dsimp [n]; omega
    have hX₃ : X₃.level ≤ n := by dsimp [n]; omega
    have hZ₁₂ : Z₁₂.level ≤ n := by dsimp [n]; omega
    have hZ₂₃ : Z₂₃.level ≤ n := by dsimp [n]; omega
    have hZ₁₃ : Z₁₃.level ≤ n := by dsimp [n]; omega
    have comm' : homEquiv T _ _ n hX₁ hX₂ u₁₂ ≫ homEquiv T _ _ n hX₂ hX₃ u₂₃ =
        homEquiv T _ _ n hX₁ hX₃ u₁₃ := by
      rw [← homEquiv_comp T _ _ n hX₁ hX₂ hX₃, comm]
    have h₁₂' := (distinguished_iff T (Triangle.mk u₁₂ v₁₂ w₁₂) n hX₁ hX₂ hZ₁₂).1 h₁₂
    have h₂₃' := (distinguished_iff T (Triangle.mk u₂₃ v₂₃ w₂₃) n hX₂ hX₃ hZ₂₃).1 h₂₃
    have h₁₃' := (distinguished_iff T (Triangle.mk u₁₃ v₁₃ w₁₃) n hX₁ hX₃ hZ₁₃).1 h₁₃
    obtain ⟨o⟩ := IsTriangulated.octahedron_axiom comm' h₁₂' h₂₃' h₁₃'
    let m₁ : stage T Z₁₂ n ⟶ stage T Z₁₃ n := o.m₁
    let m₃ : stage T Z₁₃ n ⟶ stage T Z₂₃ n := o.m₃
    refine ⟨{
      m₁ := (homEquiv T _ _ n hZ₁₂ hZ₁₃).symm m₁
      m₃ := (homEquiv T _ _ n hZ₁₃ hZ₂₃).symm m₃
      comm₁ := ?_
      comm₂ := ?_
      comm₃ := ?_
      comm₄ := ?_
      mem := ?_ }⟩
    · apply hom_ext T n hX₂ hZ₁₃
      rw [homEquiv_comp T _ _ n hX₂ hZ₁₂ hZ₁₃,
        homEquiv_comp T _ _ n hX₂ hX₃ hZ₁₃, Equiv.apply_symm_apply]
      exact o.comm₁
    · apply hom_ext T (X := Z₁₂) (Y := X₁⟦(1 : ℤ)⟧) n hZ₁₂ hX₁
      rw [homEquiv_comp T ((homEquiv T _ _ n hZ₁₂ hZ₁₃).symm m₁) w₁₃ n hZ₁₂ hZ₁₃ hX₁,
        Equiv.apply_symm_apply]
      apply (cancel_mono (stageShiftIso T 1 X₁ n).hom).1
      rw [Category.assoc]
      exact o.comm₂
    · apply hom_ext T n hX₃ hZ₂₃
      rw [homEquiv_comp T _ _ n hX₃ hZ₁₃ hZ₂₃, Equiv.apply_symm_apply]
      exact o.comm₃
    · apply hom_ext T (X := Z₁₃) (Y := X₂⟦(1 : ℤ)⟧) n hZ₁₃ hX₂
      rw [homEquiv_comp T w₁₃ (u₁₂⟦(1 : ℤ)⟧') n hZ₁₃ hX₁ hX₂,
        homEquiv_comp T ((homEquiv T _ _ n hZ₁₃ hZ₂₃).symm m₃) w₂₃ n hZ₁₃ hZ₂₃ hX₂,
        Equiv.apply_symm_apply,
        homEquiv_shift T 1 u₁₂ n hX₁ hX₂]
      have e := congrArg (fun f => f ≫ (stageShiftIso T 1 X₂ n).inv) o.comm₄
      simp only [Triangle.mk_mor₃, Triangle.mk_obj₁, Triangle.mk_obj₃,
        Category.assoc] at e
      erw [Iso.hom_inv_id, Category.comp_id] at e
      simpa only [Category.assoc] using e
    · apply (distinguished_iff T _ n hZ₁₂ hZ₁₃ hZ₂₃).2
      change Triangle.mk
        (homEquiv T Z₁₂ Z₁₃ n hZ₁₂ hZ₁₃ ((homEquiv T _ _ n hZ₁₂ hZ₁₃).symm m₁))
        (homEquiv T Z₁₃ Z₂₃ n hZ₁₃ hZ₂₃ ((homEquiv T _ _ n hZ₁₃ hZ₂₃).symm m₃))
        (homEquiv T Z₂₃ (Z₁₂⟦(1 : ℤ)⟧) n hZ₂₃ hZ₁₂ (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧') ≫
          (stageShiftIso T 1 Z₁₂ n).hom) ∈ distTriang C
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      erw [homEquiv_comp T w₂₃ (v₁₂⟦(1 : ℤ)⟧') n hZ₂₃ hX₂ hZ₁₂,
        homEquiv_shift T 1 v₁₂ n hX₂ hZ₁₂]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id, Category.comp_id]
      simpa only [stageTriangle, Triangle.mk_mor₃, Triangle.mk_mor₂, Triangle.mk_obj₁,
        Triangle.mk_obj₂, Triangle.mk_obj₃, Category.assoc] using o.mem

end CategoryTheory.Stabilization
