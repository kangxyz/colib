/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.TensorNegExtendComponent
/-! # The actual unit comparison for chain-to-cochain extension -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
namespace HomologicalComplex.TensorNegExtend
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C]

/-- The original extension of the native chain tensor unit is the native cochain
unit, via the standard extension-of-single-complex comparison. -/
def tensorNegExtendUnitIso :
    negExtend (HomologicalComplex.tensorUnit C (.down ℕ)) ≅
      HomologicalComplex.tensorUnit C (.up ℤ) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat (𝟙_ C) 0 0 rfl

/-- The genuine unit comparison cancels the native degree-zero identifications. -/
theorem tensorNegExtendUnitIso_inv_f_zero_comp :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫
      (tensorNegExtendUnitIso (C := C)).inv.f 0 ≫
      (negExtendIso (HomologicalComplex.tensorUnit C (.down ℕ)) 0).hom =
    (singleObjXSelf (.down ℕ) 0 (𝟙_ C)).inv := by
  dsimp only [tensorNegExtendUnitIso]
  rw [extendSingleIso_inv_f]
  simp only [negExtendIso, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end HomologicalComplex.TensorNegExtend
