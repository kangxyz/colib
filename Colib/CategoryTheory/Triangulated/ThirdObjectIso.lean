/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Colib.Util.References

/-! # Transporting the third object of a triangle -/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type*} [Category* C] [HasShift C ℤ]

/-- Replace the third object using the specified isomorphism. The adjacent maps are
transported along its forward and inverse morphisms. -/
@[colib_tag "COL-1238"]
def ofIso₃ (T : Triangle C) {Z : C} (e : T.obj₃ ≅ Z) : Triangle C :=
  Triangle.mk T.mor₁ (T.mor₂ ≫ e.hom) (e.inv ≫ T.mor₃)

/-- The comparison with the original triangle has identity components at the first
two objects and the specified isomorphism at the third. -/
@[colib_tag "COL-1238"]
def isoOfIso₃ (T : Triangle C) {Z : C} (e : T.obj₃ ≅ Z) : T ≅ T.ofIso₃ e := by
  refine Triangle.isoMk T (T.ofIso₃ e) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ T.mor₁
    rw [Category.comp_id, Category.id_comp]
  · change T.mor₂ ≫ e.hom = 𝟙 _ ≫ (T.mor₂ ≫ e.hom)
    exact (Category.id_comp _).symm
  · let S := CategoryTheory.shiftFunctor C (1 : ℤ)
    change T.mor₃ ≫ S.map (𝟙 T.obj₁) = e.hom ≫ e.inv ≫ T.mor₃
    rw [S.map_id, Category.comp_id, e.hom_inv_id_assoc]

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The transport of the third object preserves distinguished triangles. -/
@[colib_tag "COL-1238", stacks 0145 "TR1, transport through the third-object isomorphism"]
theorem ofIso₃_distinguished (T : Triangle C) {Z : C} (e : T.obj₃ ≅ Z)
    (hT : T ∈ distTriang C) : T.ofIso₃ e ∈ distTriang C :=
  (distinguished_iff_of_iso (T.isoOfIso₃ e)).1 hT

/-- For a composite through an inverse triangle comparison, the specified endpoint
components and an isomorphism identifying the middle component detect invertibility
at the third vertex. -/
theorem isIso_comp_inv_hom₃_of_components {S P T U : Triangle C}
    (s : S ⟶ P) (e : T ≅ P) (c : T ⟶ U) (hs : S ∈ distTriang C) (hu : U ∈ distTriang C)
    {B : C} (d : U.obj₂ ≅ B) (b : S.obj₂ ≅ B)
    {a₁ : S.obj₁ ⟶ P.obj₁} {a₃ : S.obj₃ ⟶ P.obj₃}
    {b₁ : T.obj₁ ≅ P.obj₁} {b₃ : T.obj₃ ≅ P.obj₃}
    (hs₁ : s.hom₁ = a₁) (he₁ : e.hom.hom₁ = b₁.hom)
    (hs₃ : s.hom₃ = a₃) (he₃ : e.hom.hom₃ = b₃.hom)
    (h₁ : IsIso (a₁ ≫ b₁.inv ≫ c.hom₁))
    (h₂ : (s.hom₂ ≫ e.inv.hom₂ ≫ c.hom₂) ≫ d.hom = b.hom) :
    IsIso (a₃ ≫ b₃.inv ≫ c.hom₃) := by
  have h₁e : Triangle.π₁.mapIso e = b₁ := Iso.ext he₁
  have h₃e : Triangle.π₃.mapIso e = b₃ := Iso.ext he₃
  have h₁i : e.inv.hom₁ = b₁.inv := congrArg Iso.inv h₁e
  have h₃i : e.inv.hom₃ = b₃.inv := congrArg Iso.inv h₃e
  have h₁c : s.hom₁ ≫ e.inv.hom₁ ≫ c.hom₁ = a₁ ≫ b₁.inv ≫ c.hom₁ :=
    congrArg₂ (fun f g => f ≫ g ≫ c.hom₁) hs₁ h₁i
  have h₃c : s.hom₃ ≫ e.inv.hom₃ ≫ c.hom₃ = a₃ ≫ b₃.inv ≫ c.hom₃ :=
    congrArg₂ (fun f g => f ≫ g ≫ c.hom₃) hs₃ h₃i
  exact (congrArg IsIso h₃c).mp
    (isIso₃_of_isIso₁₂ (s ≫ e.inv ≫ c) hs hu
      ((congrArg IsIso h₁c).mpr h₁) (IsIso.of_isIso_fac_right h₂))

end CategoryTheory.Pretriangulated.Triangle
