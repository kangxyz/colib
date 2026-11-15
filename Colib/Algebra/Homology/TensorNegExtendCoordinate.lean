/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.TensorNegExtendRightUnit
public import Colib.Algebra.Homology.TensorNegExtendNaturality
/-! # Native unit-coordinate insertion under chain-to-cochain extension -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
namespace HomologicalComplex.TensorNegExtend
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{0} C]

/-- The original chain insertion becomes the actual cochain unit-coordinate
insertion, through the native unit and total-tensor extension comparisons. -/
theorem tensorNegExtendFullIso_unitCoordinate {K L M : ChainComplex C ℕ}
    (a : K ⟶ L) (b : HomologicalComplex.tensorUnit C (.down ℕ) ⟶ M) :
    extendMap ((HomologicalComplex.rightUnitor K).inv ≫
      HomologicalComplex.tensorHom a b) ComplexShape.embeddingDownNat =
    (HomologicalComplex.rightUnitor (negExtend K)).inv ≫
      HomologicalComplex.tensorHom (extendMap a ComplexShape.embeddingDownNat)
        ((tensorNegExtendUnitIso (C := C)).inv ≫
          extendMap b ComplexShape.embeddingDownNat) ≫
      (tensorNegExtendFullIso L M).hom := by
  have hcomp : HomologicalComplex.tensorHom (𝟙 (negExtend K))
        (tensorNegExtendUnitIso (C := C)).inv ≫
      HomologicalComplex.tensorHom (extendMap a ComplexShape.embeddingDownNat)
        (extendMap b ComplexShape.embeddingDownNat) =
      HomologicalComplex.tensorHom (extendMap a ComplexShape.embeddingDownNat)
        ((tensorNegExtendUnitIso (C := C)).inv ≫
          extendMap b ComplexShape.embeddingDownNat) := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine HomologicalComplex.mapBifunctor.hom_ext fun i j h => ?_
    simp [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
      whisker_exchange_assoc]
  rw [extendMap_comp, tensorNegExtendFullIso_rightUnitor]
  simp only [Category.assoc]
  rw [← tensorNegExtendFullIso_naturality a b]
  rw [← Category.assoc _ _ (tensorNegExtendFullIso L M).hom, hcomp]

end HomologicalComplex.TensorNegExtend
