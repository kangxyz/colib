/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenCarrier

/-!
# Descent of actual displayed seed-carrier cell maps

The two original displayed pushouts glue one supplied continuous Laurent map and two supplied
continuous cylinders. Only their four actual endpoint equations are needed. The descended map
retains each entire cylinder and both separate tips; no homotopy or filler is selected.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology TopCat SSet
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedCarrierDesc
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
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


variable {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor) (Z : TopCat.{u})
  (L : C(|parameterSSet G|, Z)) (C₀ C₁ : C(|parameterSSet F| × unitInterval, Z)) (z₀ z₁ : Z)
  (h₀ : ∀ y, C₀ (y, 0) = L (mapParameter (attachPostcompNode F J G ε₀) y))
  (h₁ : ∀ y, C₀ (y, 1) = z₀)
  (k₀ : ∀ y, C₁ (y, 0) = L (mapParameter (attachPostcompNode F J G ε₁) y))
  (k₁ : ∀ y, C₁ (y, 1) = z₁)

/-- A displayed cylinder keeps exactly its original ordinary interval coordinate. -/
def cylinderMap (C : C(|parameterSSet F| × unitInterval, Z)) :
    |parameterSSet F| ⊗ TopCat.I ⟶ Z :=
  TopCat.ofHom ⟨fun y => C (y.1, y.2.down), by fun_prop⟩

/-- The original Laurent map and ordinary tip define the first endpoint map. -/
def firstEnds : TopCat.of (|parameterSSet G| ⊕ |tipSSet.{u}|) ⟶ Z :=
  TopCat.ofHom ⟨Sum.elim L (fun _ => z₀),
    continuous_sum_dom.mpr ⟨L.continuous, continuous_const⟩⟩

include h₀ h₁ in
/-- Both first displayed cylinder ends agree with the supplied actual cell maps. -/
theorem first_square :
    TopCat.intervalEndpoints |parameterSSet F| ≫ cylinderMap F Z C₀ =
      DoubleCylinder.endMap (SSet.toTop.map (attaching F J G ε₀))
        (SSet.toTop.map (erase F)) ≫ firstEnds G Z L z₀ := by
  ext y
  rcases y with y | y
  · exact h₀ y
  · exact h₁ y

/-- The actual first displayed pushout glues the entire ordinary cylinder. -/
def firstMap : |firstSimplicial F J G ε₀| ⟶ Z :=
  (first_isPushout F J G ε₀).desc (cylinderMap F Z C₀) (firstEnds G Z L z₀)
    (first_square F J G ε₀ Z L C₀ z₀ h₀ h₁)

/-- Every point of the first original cylinder retains the supplied whole value. -/
theorem first_cylinder (y : |parameterSSet F|) (s : unitInterval) :
    firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁
      (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F)
        (y, ULift.up s)) = C₀ (y, s) :=
  ConcreteCategory.congr_hom ((first_isPushout F J G ε₀).inl_desc
    (cylinderMap F Z C₀) (firstEnds G Z L z₀)
    (first_square F J G ε₀ Z L C₀ z₀ h₀ h₁)) (y, ULift.up s)

/-- The actual first endpoint-pair map retains both original summands. -/
theorem first_ends (y : |parameterSSet G| ⊕ |tipSSet.{u}|) :
    firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁
      (DoubleCylinder.realizedEnds (attaching F J G ε₀) (erase F) y) =
      firstEnds G Z L z₀ y :=
  ConcreteCategory.congr_hom ((first_isPushout F J G ε₀).inr_desc
    (cylinderMap F Z C₀) (firstEnds G Z L z₀)
    (first_square F J G ε₀ Z L C₀ z₀ h₀ h₁)) y

/-- The original Laurent summand is precisely its supplied whole continuous map. -/
theorem first_left (y : |parameterSSet G|) :
    firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁ (SSet.toTop.map (left₀ F J G ε₀) y) = L y :=
  (congrArg (firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁)
    (realized_left (attaching F J G ε₀) (erase F) y)).trans
      (first_ends F J G ε₀ Z L C₀ z₀ h₀ h₁ (Sum.inl y))

/-- The original ordinary tip is precisely its own supplied endpoint. -/
theorem first_right (y : |tipSSet.{u}|) :
    firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁ (SSet.toTop.map (right₀ F J G ε₀) y) = z₀ :=
  (congrArg (firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁)
    (realized_right (attaching F J G ε₀) (erase F) y)).trans
      (first_ends F J G ε₀ Z L C₀ z₀ h₀ h₁ (Sum.inr y))

/-- The first descended map and distinct second tip form the second endpoint map. -/
def secondEnds : TopCat.of (|firstSimplicial F J G ε₀| ⊕ |tipSSet.{u}|) ⟶ Z :=
  TopCat.ofHom ⟨Sum.elim (firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁) (fun _ => z₁),
    continuous_sum_dom.mpr
      ⟨(firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁).hom.continuous, continuous_const⟩⟩

include k₀ k₁ in
/-- The original shifted attachment and distinct terminal tip satisfy the second full square. -/
theorem second_square :
    TopCat.intervalEndpoints |parameterSSet F| ≫ cylinderMap F Z C₁ =
      DoubleCylinder.endMap (SSet.toTop.map (secondAttaching F J G ε₀ ε₁))
        (SSet.toTop.map (erase F)) ≫ secondEnds F J G ε₀ Z L C₀ z₀ z₁ h₀ h₁ := by
  ext y
  rcases y with y | y
  · change C₁ (y, 0) = firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁
      (SSet.toTop.map (attaching F J G ε₁ ≫ left₀ F J G ε₀) y)
    rw [Functor.map_comp]
    exact (k₀ y).trans (first_left F J G ε₀ Z L C₀ z₀ h₀ h₁ _).symm
  · exact k₁ y

/-- Both actual displayed pushouts descend the supplied whole cell maps. -/
def map : space F J G ε₀ ε₁ ⟶ Z :=
  (second_isPushout F J G ε₀ ε₁).desc (cylinderMap F Z C₁)
    (secondEnds F J G ε₀ Z L C₀ z₀ z₁ h₀ h₁)
    (second_square F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁)

private theorem map_ends (y : |firstSimplicial F J G ε₀| ⊕ |tipSSet.{u}|) :
    map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁
      (DoubleCylinder.realizedEnds (secondAttaching F J G ε₀ ε₁) (erase F) y) =
      secondEnds F J G ε₀ Z L C₀ z₀ z₁ h₀ h₁ y :=
  ConcreteCategory.congr_hom ((second_isPushout F J G ε₀ ε₁).inr_desc
    (cylinderMap F Z C₁) (secondEnds F J G ε₀ Z L C₀ z₀ z₁ h₀ h₁)
    (second_square F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁)) y

/-- Every point of the first whole sheet retains the original descended first-map value. -/
theorem map_first (y : |firstSimplicial F J G ε₀|) :
    map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁
      (SSet.toTop.map (left₁ F J G ε₀ ε₁) y) =
      firstMap F J G ε₀ Z L C₀ z₀ h₀ h₁ y :=
  (congrArg (map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁)
    (realized_left (secondAttaching F J G ε₀ ε₁) (erase F) y)).trans
      (map_ends F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁ (Sum.inl y))

/-- The entire original Laurent inclusion has exactly the supplied value. -/
theorem map_laurent (y : |parameterSSet G|) :
    map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁
      (laurentInclusion F J G ε₀ ε₁ y) = L y :=
  (map_first F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁ _).trans
    (first_left F J G ε₀ Z L C₀ z₀ h₀ h₁ y)

/-- Every ordinary cylinder point preserves the supplied whole parameter and its exact height. -/
theorem map_cylinderMinus (y : |parameterSSet F|) (s : unitInterval) :
    map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁
      (cylinderMinus F J G ε₀ ε₁ (y, s)) = C₀ (y, s) :=
  (map_first F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁ _).trans
    (first_cylinder F J G ε₀ Z L C₀ z₀ h₀ h₁ y s)

/-- Every shifted cylinder point preserves its independently supplied whole value. -/
theorem map_cylinderPlus (y : |parameterSSet F|) (s : unitInterval) :
    map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁
      (cylinderPlus F J G ε₀ ε₁ (y, s)) = C₁ (y, s) :=
  ConcreteCategory.congr_hom ((second_isPushout F J G ε₀ ε₁).inl_desc
    (cylinderMap F Z C₁) (secondEnds F J G ε₀ Z L C₀ z₀ z₁ h₀ h₁)
    (second_square F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁)) (y, ULift.up s)

/-- The first original tip retains its own specified endpoint. -/
theorem map_tipMinus :
    map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁
      (tipMinus F J G ε₀ ε₁) = z₀ :=
  (map_first F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁ _).trans
    (first_right F J G ε₀ Z L C₀ z₀ h₀ h₁ _)

/-- The second original tip retains its separately specified endpoint. -/
theorem map_tipPlus :
    map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁
      (tipPlus F J G ε₀ ε₁) = z₁ :=
  (congrArg (map F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁)
    (realized_right (secondAttaching F J G ε₀ ε₁) (erase F) default)).trans
      (map_ends F J G ε₀ ε₁ Z L C₀ C₁ z₀ z₁ h₀ h₁ k₀ k₁ (Sum.inr default))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedCarrierDesc
