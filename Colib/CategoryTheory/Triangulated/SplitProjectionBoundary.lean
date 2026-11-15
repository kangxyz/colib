/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The boundary of a split projection -/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

universe u v

/-- Projecting the boundary of a split projection onto the shifted complementary
summand gives an isomorphism. -/
theorem isIso_boundary_reducedProjection
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A B G R X : C} (f : G ⟶ A) (e : A ≅ B) (g : A ⟶ X) (δ : X ⟶ G⟦(1 : ℤ)⟧)
    (p : G ⟶ B) (s : B ⟶ G) (q : G ⟶ R) (i : R ⟶ G)
    (hp : f ≫ e.hom = p) (hs : s ≫ p = 𝟙 B) (hq : i ≫ q = 𝟙 R)
    (hi : q ≫ i = 𝟙 G - p ≫ s) (hT : Triangle.mk f g δ ∈ distTriang C) :
    IsIso (δ ≫ q⟦(1 : ℤ)⟧') := by
  have hip : i ≫ p = 0 := by
    have h : (q ≫ i) ≫ p = 0 := by
      rw [hi, Preadditive.sub_comp, Category.id_comp, Category.assoc, hs,
        Category.comp_id, sub_self]
    simpa only [← Category.assoc, hq, Category.id_comp, comp_zero] using
      congrArg (i ≫ ·) h
  have hsq : s ≫ q = 0 := by
    have h : s ≫ (q ≫ i) = 0 := by
      rw [hi, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hs,
        Category.id_comp, sub_self]
    simpa only [Category.assoc, hq, Category.comp_id, zero_comp] using
      congrArg (· ≫ q) h
  let e₁ : G ≅ R ⊞ B :=
    { hom := biprod.lift q p
      inv := biprod.desc i s
      hom_inv_id := by rw [biprod.lift_desc, hi, sub_add_cancel]
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [hip, hsq, hs, hq] }
  let T := Triangle.mk f g δ
  let U := (binaryBiproductTriangle R B).rotate
  have hU : U ∈ distTriang C := rot_of_distTriang _ (binaryBiproductTriangle_distinguished R B)
  have hcomm : T.mor₁ ≫ e.hom = e₁.hom ≫ U.mor₁ := by
    change f ≫ e.hom = biprod.lift q p ≫ biprod.snd
    rw [hp, biprod.lift_snd]
  let a := isoTriangleOfIso₁₂ T U hT hU e₁ e hcomm
  let a₃ : X ≅ R⟦(1 : ℤ)⟧ := Triangle.π₃.mapIso a
  have ha : a.hom.hom₁ = e₁.hom := isoTriangleOfIso₁₂_hom_hom₁ T U hT hU e₁ e hcomm
  have h₃ := a.hom.comm₃
  rw [ha] at h₃
  change δ ≫ (biprod.lift q p)⟦(1 : ℤ)⟧' =
    a₃.hom ≫ (-(biprod.inl : R ⟶ R ⊞ B)⟦(1 : ℤ)⟧') at h₃
  have hsign := congrArg (· ≫ (biprod.fst : R ⊞ B ⟶ R)⟦(1 : ℤ)⟧') h₃
  simp only [Category.assoc, ← Functor.map_comp, biprod.lift_fst,
    Preadditive.neg_comp, Preadditive.comp_neg, biprod.inl_fst] at hsign
  rw [(shiftFunctor C (1 : ℤ)).map_id R, Category.comp_id] at hsign
  rw [hsign]
  exact (inferInstance : IsIso (-a₃).hom)

end CategoryTheory.Pretriangulated
