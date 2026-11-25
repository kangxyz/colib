/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenCarrier
public import Colib.Topology.DoubleMappingCylinder.Invariance

/-! Maps of two-tip carriers from two full attachment squares, retaining each cell clock. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Waldhausen Topology TopCat SSet CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenMap
open CutOpenCarrier
private theorem realized_left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (y : |Y|) :
    SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) y =
        DoubleCylinder.realizedEnds f g (Sum.inl y) := by
  have h : SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inl ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inl Y Z)
  exact ConcreteCategory.congr_hom h y

private theorem realized_right {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (z : |Z|) :
    SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) z =
        DoubleCylinder.realizedEnds f g (Sum.inr z) := by
  have h : SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inr ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inr Y Z)
  exact ConcreteCategory.congr_hom h z


variable {V W T V' W' T' : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (F' : V' ⟶ W') (J' : W' ⟶ T') (G' : V' ⟶ T')
  (ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)
  (η₀ η₁ : G'.hom.toFunctor ≅ (F' ≫ J').hom.toFunctor)
  (u : |parameterSSet F| ⟶ |parameterSSet F'|)
  (v : |parameterSSet G| ⟶ |parameterSSet G'|)
  (h₀ : SSet.toTop.map (attaching F J G ε₀) ≫ v =
    u ≫ SSet.toTop.map (attaching F' J' G' η₀))
  (h₁ : SSet.toTop.map (attaching F J G ε₁) ≫ v =
    u ≫ SSet.toTop.map (attaching F' J' G' η₁))

/-- Both sheet maps preserve their separate terminal tip. -/
theorem erase_square :
    SSet.toTop.map (erase F) ≫ 𝟙 _ = u ≫ SSet.toTop.map (erase F') := by
  ext x
  exact Subsingleton.elim _ _

/-- The ordinary sheet map is the existing strict map of its actual displayed double cylinders. -/
def firstMap : |firstSimplicial F J G ε₀| ⟶
    |firstSimplicial F' J' G' η₀| :=
  DoubleCylinder.map (first_isPushout F J G ε₀)
    (first_isPushout F' J' G' η₀)
    u v (𝟙 _)
    h₀ (erase_square F F' u)

@[reassoc] theorem firstMap_left :
    SSet.toTop.map (left₀ F J G ε₀) ≫ firstMap F J G F' J' G' ε₀ η₀ u v h₀ =
      v ≫ SSet.toTop.map (left₀ F' J' G' η₀) := by
  ext x
  have e₀ := realized_left (attaching F J G ε₀) (erase F) x
  have e₁ := realized_left (attaching F' J' G' η₀)
    (erase F') (v x)
  exact (congrArg (firstMap F J G F' J' G' ε₀ η₀ u v h₀) e₀).trans
    ((DoubleCylinder.map_left _ _ _ _ _ _ _ x).trans e₁.symm)

@[reassoc] theorem firstMap_right :
    SSet.toTop.map (right₀ F J G ε₀) ≫ firstMap F J G F' J' G' ε₀ η₀ u v h₀ =
      SSet.toTop.map (right₀ F' J' G' η₀) := by
  ext x
  have e₀ := realized_right (attaching F J G ε₀) (erase F) x
  have e₁ := realized_right (attaching F' J' G' η₀)
    (erase F') x
  exact (congrArg (firstMap F J G F' J' G' ε₀ η₀ u v h₀) e₀).trans
    ((DoubleCylinder.map_right _ _ _ _ _ _ _ x).trans e₁.symm)

include h₁ in
/-- The shifted sheet uses its own full anchor, followed by the already checked ordinary map. -/
theorem second_square :
    SSet.toTop.map (secondAttaching F J G ε₀ ε₁) ≫ firstMap F J G F' J' G' ε₀ η₀ u v h₀ =
      u ≫ SSet.toTop.map
        (secondAttaching F' J' G' η₀ η₁) := by
  dsimp only [secondAttaching]
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, firstMap_left,
    ← Category.assoc, h₁, Category.assoc]

/-- Two applications of the existing double-cylinder map retain the complete original carrier. -/
def map : space F J G ε₀ ε₁ ⟶
    space F' J' G' η₀ η₁ :=
  DoubleCylinder.map (second_isPushout F J G ε₀ ε₁)
    (second_isPushout F' J' G' η₀ η₁)
    u (firstMap F J G F' J' G' ε₀ η₀ u v h₀) (𝟙 _)
    (second_square F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁) (erase_square F F' u)

@[reassoc] theorem map_first :
    SSet.toTop.map (left₁ F J G ε₀ ε₁) ≫ map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁ =
      firstMap F J G F' J' G' ε₀ η₀ u v h₀ ≫ SSet.toTop.map
        (left₁ F' J' G' η₀ η₁) := by
  ext x
  have e₀ := realized_left (secondAttaching F J G ε₀ ε₁) (erase F) x
  have e₁ := realized_left
    (secondAttaching F' J' G' η₀ η₁)
    (erase F') (firstMap F J G F' J' G' ε₀ η₀ u v h₀ x)
  exact (congrArg (map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁) e₀).trans
    ((DoubleCylinder.map_left _ _ _ _ _ _ _ x).trans e₁.symm)

@[simp] theorem map_tipPlus :
    map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁ (tipPlus F J G ε₀ ε₁) =
      tipPlus F' J' G' η₀ η₁ := by
  have e₀ := realized_right (secondAttaching F J G ε₀ ε₁) (erase F)
    (default : |tipSSet.{u}|)
  have e₁ := realized_right
    (secondAttaching F' J' G' η₀ η₁)
    (erase F') (default : |tipSSet.{u}|)
  exact (congrArg (map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁) e₀).trans
    ((DoubleCylinder.map_right _ _ _ _ _ _ _ _).trans e₁.symm)

@[simp] theorem map_tipMinus :
    map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁ (tipMinus F J G ε₀ ε₁) =
      tipMinus F' J' G' η₀ η₁ := by
  have e₀ := ConcreteCategory.congr_hom (map_first F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁)
    (SSet.toTop.map (right₀ F J G ε₀) (default : |tipSSet.{u}|))
  have e₁ := ConcreteCategory.congr_hom (firstMap_right F J G F' J' G' ε₀ η₀ u v h₀)
    (default : |tipSSet.{u}|)
  exact e₀.trans (congrArg (SSet.toTop.map
    (left₁ F' J' G' η₀ η₁)) e₁)

@[simp] theorem map_laurent (x : |parameterSSet G|) :
    map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁ (laurentInclusion F J G ε₀ ε₁ x) =
      laurentInclusion F' J' G' η₀ η₁
        (v x) := by
  have e₀ := ConcreteCategory.congr_hom (map_first F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁)
    (SSet.toTop.map (left₀ F J G ε₀) x)
  have e₁ := ConcreteCategory.congr_hom (firstMap_left F J G F' J' G' ε₀ η₀ u v h₀) x
  exact e₀.trans (congrArg (SSet.toTop.map
    (left₁ F' J' G' η₀ η₁)) e₁)

@[simp] theorem map_cylinderMinus (x : |parameterSSet F|) (t : unitInterval) :
    map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁ (cylinderMinus F J G ε₀ ε₁ (x, t)) =
      cylinderMinus F' J' G' η₀ η₁
        (u x, t) := by
  have e₀ := ConcreteCategory.congr_hom (map_first F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁)
    (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F) (x, ULift.up t))
  have e₁ := DoubleCylinder.map_cylinder_apply (first_isPushout F J G ε₀)
    (first_isPushout F' J' G' η₀)
    u v (𝟙 _)
    h₀ (erase_square F F' u) x (ULift.up t)
  exact e₀.trans (congrArg (SSet.toTop.map
    (left₁ F' J' G' η₀ η₁)) e₁)

@[simp] theorem map_cylinderPlus (x : |parameterSSet F|) (t : unitInterval) :
    map F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁ (cylinderPlus F J G ε₀ ε₁ (x, t)) =
      cylinderPlus F' J' G' η₀ η₁
        (u x, t) :=
  DoubleCylinder.map_cylinder_apply (second_isPushout F J G ε₀ ε₁)
    (second_isPushout F' J' G' η₀ η₁)
    u (firstMap F J G F' J' G' ε₀ η₀ u v h₀) (𝟙 _)
    (second_square F J G F' J' G' ε₀ ε₁ η₀ η₁ u v h₀ h₁) (erase_square F F' u) x (ULift.up t)

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenMap
