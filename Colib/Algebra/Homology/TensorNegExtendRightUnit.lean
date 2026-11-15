/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.TensorNegExtendUnit
/-! # Right-unit compatibility of the native extension tensor comparison -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
namespace HomologicalComplex.TensorNegExtend
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{0} C]

/-- Extension preserves the native right-unit insertion through its actual unit
comparison and the original total-tensor extension comparison. -/
theorem tensorNegExtendFullIso_rightUnitor (K : ChainComplex C ℕ) :
    extendMap (HomologicalComplex.rightUnitor K).inv ComplexShape.embeddingDownNat =
      (HomologicalComplex.rightUnitor (negExtend K)).inv ≫
        HomologicalComplex.tensorHom (𝟙 (negExtend K))
          (tensorNegExtendUnitIso (C := C)).inv ≫
        (tensorNegExtendFullIso K (HomologicalComplex.tensorUnit C (.down ℕ))).hom := by
  ext i : 1
  by_cases hi : 0 < i
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat i
      (by intro n; change -(n : ℤ) ≠ i; omega)).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  simp only [HomologicalComplex.comp_f]
  erw [extendMap_f (HomologicalComplex.rightUnitor K).inv
    ComplexShape.embeddingDownNat (i := n) rfl]
  change (negExtendIso K n).hom ≫ (HomologicalComplex.rightUnitor' K).inv n ≫
      (negExtendIso (HomologicalComplex.tensorObj K
        (HomologicalComplex.tensorUnit C (.down ℕ))) n).inv =
    (HomologicalComplex.rightUnitor' (negExtend K)).inv (-(n : ℤ)) ≫ _
  rw [HomologicalComplex.rightUnitor'_inv, HomologicalComplex.rightUnitor'_inv]
  simp only [Category.assoc, ι_mapBifunctorMap_assoc, curriedTensor_map_app,
    curriedTensor_obj_map, HomologicalComplex.id_f, id_whiskerRight]
  erw [Category.id_comp]
  have hι := tensorNegExtendFullIso_hom_ι K
    (HomologicalComplex.tensorUnit C (.down ℕ)) n 0 n (Nat.add_zero n)
  erw [hι]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    tensorNegExtendUnitIso_inv_f_zero_comp]
  simp only [id_tensorHom, rightUnitor_inv_comp_tensorHom_assoc]

end HomologicalComplex.TensorNegExtend
