/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels of split epimorphisms in a pretriangulated category

The distinguished triangle of a split epimorphism has zero connecting
map. The existing binary biproduct data then exhibits the first arrow
as its kernel.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A morphism with a specified section has an actual kernel. -/
theorem hasKernel_of_section {A X : D} (r : A ⟶ X) (s : X ⟶ A)
    (hs : s ≫ r = 𝟙 X) : HasKernel r := by
  obtain ⟨Z, i, δ, hT⟩ := distinguished_cocone_triangle₁ r
  let T := Triangle.mk i r δ
  have hrδ : r ≫ δ = 0 := comp_distTriang_mor_zero₂₃ T hT
  have hδ : δ = 0 := by rw [← Category.id_comp δ, ← hs, Category.assoc, hrδ, comp_zero]
  have hi : i ≫ r = 0 := comp_distTriang_mor_zero₁₂ T hT
  have htotal : (𝟙 A - r ≫ s) ≫ r = 0 := by
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs,
      Category.comp_id, sub_self]
  obtain ⟨p, hp⟩ := T.coyoneda_exact₂ hT (𝟙 A - r ≫ s) htotal
  have hp' : p ≫ i = 𝟙 A - r ≫ s := hp.symm
  let data := binaryBiproductData T hT hδ s hs p (by
    change p ≫ i + r ≫ s = 𝟙 A
    rw [hp', sub_add_cancel])
  have hip : i ≫ p = 𝟙 Z := data.bicone.inl_fst
  let : IsSplitMono i := IsSplitMono.mk' ⟨p, hip⟩
  refine ⟨⟨⟨KernelFork.ofι i hi, KernelFork.IsLimit.ofι' i hi ?_⟩⟩⟩
  intro W q hq
  refine ⟨q ≫ p, ?_⟩
  rw [Category.assoc, hp', Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    hq, zero_comp, sub_zero]

end CategoryTheory.Pretriangulated
