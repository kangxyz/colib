/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderBoundary

/-!
# Changing the pointed cylinder parameter

The induced map of the literal pointed cylinders preserves the
projections. A global point of the parameter gives the original section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- The product leg of the original pointed cylinder quotient. -/
abbrev cylinderProductLeg (X : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w}) :
    X.right ⨯ I ⟶ (parameterizedCylinder X I).right :=
  pushout.inl (intervalAxis X I) (terminal.from I)

variable (I : Cᵒᵖ ⥤ SSet.{w})

/-- The quotient map collapses the original basepoint axis. -/
@[reassoc]
theorem intervalAxis_cylinderProductLeg (X : PointedSimplicialPresheaf.{w} C) :
    intervalAxis X I ≫ cylinderProductLeg X I =
      terminal.from I ≫ (parameterizedCylinder X I).hom :=
  pushout.condition

/-- The product leg retains the original section graph. -/
theorem cylinderSection_right_productLeg (X : PointedSimplicialPresheaf.{w} C)
    (s : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ I) :
    (cylinderSection X s).right =
      prod.lift (𝟙 X.right) (terminal.from X.right ≫ s) ≫ cylinderProductLeg X I :=
  rfl

/-- The quotient retains the actual map of products in the base. -/
@[reassoc]
theorem cylinderProductLeg_parameterizedCylinderMap {X Y : PointedSimplicialPresheaf.{w} C}
    (i : X ⟶ Y) :
    cylinderProductLeg X I ≫ (parameterizedCylinderMap i I).right =
      prod.map i.right (𝟙 I) ≫ cylinderProductLeg Y I :=
  pushout.inl_desc _ _ _

/-- Changing the parameter acts by the original map of products and
its induced map after collapsing the basepoint axis. -/
def parameterizedCylinderParameterMap {I' : Cᵒᵖ ⥤ SSet.{w}} (f : I ⟶ I')
    (X : PointedSimplicialPresheaf.{w} C) :
    parameterizedCylinder X I ⟶ parameterizedCylinder X I' :=
  Under.homMk (pushout.map (intervalAxis X I) (terminal.from I) (intervalAxis X I')
    (terminal.from I') (prod.map (𝟙 X.right) f) (𝟙 _) f
    (by apply prod.hom_ext <;> simp [intervalAxis])
    (by simp))
    (by simp)

/-- The map of parameters retains the original map of products. -/
@[reassoc]
theorem cylinderProductLeg_parameterizedCylinderParameterMap {I' : Cᵒᵖ ⥤ SSet.{w}}
    (f : I ⟶ I') (X : PointedSimplicialPresheaf.{w} C) :
    cylinderProductLeg X I ≫
        (parameterizedCylinderParameterMap I f X).right =
      prod.map (𝟙 X.right) f ≫ cylinderProductLeg X I' :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem parameterizedCylinderParameterMap_projection {I' : Cᵒᵖ ⥤ SSet.{w}} (f : I ⟶ I')
    (X : PointedSimplicialPresheaf.{w} C) :
    parameterizedCylinderParameterMap I f X ≫ cylinderProjection X I' = cylinderProjection X I := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · simp only [parameterizedCylinderParameterMap, cylinderProjection, Under.comp_right,
      Under.homMk_right, Category.assoc, pushout.map, pushout.inl_desc_assoc, pushout.inl_desc,
      prod.map_fst, Category.comp_id]
  · simp only [parameterizedCylinderParameterMap, cylinderProjection, Under.comp_right,
      Under.homMk_right, pushout.map, Category.id_comp, pushout.inr_desc_assoc, pushout.inr_desc]

/-- The map induced by a parameter point and the original section agree
after identifying the cylinder with a terminal parameter. -/
theorem terminalParameterMap_section (s : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ I)
    (X : PointedSimplicialPresheaf.{w} C) :
    parameterizedCylinderParameterMap (⊤_ _) s X =
      cylinderProjection X (⊤_ _) ≫ cylinderSection X s := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · simp only [parameterizedCylinderParameterMap, cylinderProjection, cylinderSection,
      Under.comp_right, Under.homMk_right, pushout.map, pushout.inl_desc_assoc,
      pushout.inl_desc]
    have h : prod.map (𝟙 X.right) s =
        prod.fst ≫ prod.lift (𝟙 X.right) (terminal.from X.right ≫ s) := by
      apply prod.hom_ext
      · simp
      · have ht : (prod.snd : X.right ⨯ (⊤_ _) ⟶ ⊤_ _) = terminal.from _ :=
          terminal.hom_ext _ _
        simp [ht]
    rw [← Category.assoc, ← h]
  · exact (Under.w (parameterizedCylinderParameterMap (⊤_ _) s X)).trans
      (Under.w (cylinderProjection X (⊤_ _) ≫ cylinderSection X s)).symm

/-- The cylinder with the terminal parameter identifies with its base. -/
def terminalParameterCylinderIso (X : PointedSimplicialPresheaf.{w} C) :
    parameterizedCylinder X (⊤_ _) ≅ X where
  hom := cylinderProjection X (⊤_ _)
  inv := cylinderSection X (𝟙 _)
  hom_inv_id := by
    rw [← terminalParameterMap_section]
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change cylinderProductLeg X (⊤_ _) ≫
          (parameterizedCylinderParameterMap (⊤_ _) (𝟙 _) X).right =
        cylinderProductLeg X (⊤_ _) ≫ 𝟙 _
      rw [cylinderProductLeg_parameterizedCylinderParameterMap, prod.map_id_id,
        Category.id_comp, Category.comp_id]
    · exact (Under.w (parameterizedCylinderParameterMap (⊤_ _) (𝟙 _) X)).trans
        (Under.w (𝟙 _)).symm
  inv_hom_id := cylinderSection_projection X (𝟙 _)

end CategoryTheory.PointedSimplicialPresheaf
