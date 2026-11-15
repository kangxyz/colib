/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Monoidal.UnitCoordinateMap
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
/-! # Native chain unit-coordinate insertion under degreewise monoidal functors -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
universe v v' u u'
namespace CategoryTheory.Functor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

variable [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject I D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I D, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ n : I, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) F]


/-- The original degreewise chain functor carries the native tensor insertion
through its original unit comparison and total-complex tensorator. -/
theorem mapHomologicalComplex_unitCoordinate {K L M : HomologicalComplex C c}
    (a : K ⟶ L) (b : HomologicalComplex.tensorUnit C c ⟶ M) :
    (F.mapHomologicalComplex c).map
      ((HomologicalComplex.rightUnitor K).inv ≫ HomologicalComplex.tensorHom a b) =
    (HomologicalComplex.rightUnitor ((F.mapHomologicalComplex c).obj K)).inv ≫
      HomologicalComplex.tensorHom ((F.mapHomologicalComplex c).map a)
        ((mapHomologicalComplexUnitIso F).hom ≫ (F.mapHomologicalComplex c).map b) ≫
      (mapHomologicalComplexTensorator F L M).hom := by
  exact LaxMonoidal.map_unitCoordinate (F.mapHomologicalComplex c) a b

end CategoryTheory.Functor
