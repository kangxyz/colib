/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderParameterMap
public import Colib.CategoryTheory.Limits.PointedSmashAdjunction

/-!
# Smash with the freely pointed cylinder parameter

Distributing the product over the added point identifies the original
smash quotient with the literal pointed cylinder. The comparison
retains both the parameter maps and their global sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]
  (X : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w})

local instance leftProductPreservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (prod.functor.obj X.right) :=
  preservesColimitsOfShape_of_natIso (CartesianMonoidalCategory.tensorLeftIsoProd X.right)

private def freeParameterProductIso :
    (X.right ⨯ I) ⨿ X.right ≅ X.right ⨯ ((free C).obj I).right :=
  coprod.mapIso (Iso.refl _) (CategoryTheory.Limits.prod.rightUnitor X.right).symm ≪≫
    PreservesColimitPair.iso (prod.functor.obj X.right) I (⊤_ _)

/-- Include the original parameter into its freely pointed product. -/
abbrev freeParameterProductInclusion : X.right ⨯ I ⟶ X.right ⨯ ((free C).obj I).right :=
  prod.map (𝟙 _) (freeInclusion C I)

private abbrev productInr : X.right ⟶ X.right ⨯ ((free C).obj I).right :=
  prod.lift (𝟙 _) (terminal.from _ ≫ ((free C).obj I).hom)

@[reassoc]
private theorem productInl_eq :
    coprod.inl ≫ (freeParameterProductIso X I).hom = freeParameterProductInclusion X I := by
  let e := CategoryTheory.Limits.prod.rightUnitor X.right
  let F := prod.functor.obj X.right
  let T := (⊤_ (Cᵒᵖ ⥤ SSet.{w}))
  change coprod.inl ≫ coprod.map (𝟙 (X.right ⨯ I)) e.inv ≫
    coprodComparison F I T = F.map (coprod.inl : I ⟶ I ⨿ T)
  rw [coprod.inl_map_assoc, Category.id_comp]
  exact inl_coprodComparison F I T

@[reassoc]
private theorem productInr_eq :
    coprod.inr ≫ (freeParameterProductIso X I).hom = productInr X I := by
  let e := CategoryTheory.Limits.prod.rightUnitor X.right
  let F := prod.functor.obj X.right
  let T := (⊤_ (Cᵒᵖ ⥤ SSet.{w}))
  have h : coprod.inr ≫ coprod.map (𝟙 (X.right ⨯ I)) e.inv ≫
      coprodComparison F I T = e.inv ≫ F.map (coprod.inr : T ⟶ I ⨿ T) := by
    rw [coprod.inr_map_assoc]
    exact congrArg (e.inv ≫ ·) (inr_coprodComparison F I T)
  refine h.trans ?_
  change prod.lift (𝟙 X.right) (terminal.from X.right) ≫
    prod.map (𝟙 X.right) ((free C).obj I).hom = productInr X I
  rw [prod.lift_map, Category.id_comp]

private theorem productLegs_hom_ext {Y : Cᵒᵖ ⥤ SSet.{w}}
    {f g : X.right ⨯ ((free C).obj I).right ⟶ Y}
    (h₀ : freeParameterProductInclusion X I ≫ f = freeParameterProductInclusion X I ≫ g)
    (h₁ : productInr X I ≫ f = productInr X I ≫ g) : f = g := by
  apply (cancel_epi (freeParameterProductIso X I).hom).1
  apply coprod.hom_ext
  · simpa only [productInl_eq_assoc] using h₀
  · simpa only [productInr_eq_assoc] using h₁

private def productToCylinder :
    X.right ⨯ ((free C).obj I).right ⟶ (parameterizedCylinder X I).right :=
  (freeParameterProductIso X I).inv ≫
    coprod.desc (cylinderProductLeg X I) (terminal.from X.right ≫ (parameterizedCylinder X I).hom)

@[reassoc]
private theorem productInl_toCylinder :
    freeParameterProductInclusion X I ≫ productToCylinder X I = cylinderProductLeg X I := by
  rw [← productInl_eq, productToCylinder, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]

@[reassoc]
private theorem productInr_toCylinder :
    productInr X I ≫ productToCylinder X I =
      terminal.from X.right ≫ (parameterizedCylinder X I).hom := by
  rw [← productInr_eq, productToCylinder, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]

private abbrev parameterAxis :
    ((free C).obj I).right ⟶ X.right ⨯ ((free C).obj I).right :=
  prod.lift (terminal.from ((free C).obj I).right ≫ X.hom) (𝟙 ((free C).obj I).right)

private theorem freeInclusion_parameterAxis :
    freeInclusion C I ≫ parameterAxis X I =
      intervalAxis X I ≫ freeParameterProductInclusion X I := by
  change freeInclusion C I ≫ prod.lift (terminal.from ((free C).obj I).right ≫ X.hom)
      (𝟙 ((free C).obj I).right) =
    prod.lift (terminal.from I ≫ X.hom) (𝟙 I) ≫
      prod.map (𝟙 X.right) (freeInclusion C I)
  rw [prod.comp_lift, prod.lift_map, terminal.comp_from_assoc, Category.comp_id,
    Category.comp_id, Category.id_comp]

private theorem parameterAxis_toCylinder :
    parameterAxis X I ≫ productToCylinder X I =
      terminal.from ((free C).obj I).right ≫ (parameterizedCylinder X I).hom := by
  have h₁ : ((free C).obj I).hom ≫ parameterAxis X I = X.hom ≫ productInr X I := by
    change ((free C).obj I).hom ≫ prod.lift (terminal.from ((free C).obj I).right ≫ X.hom)
        (𝟙 ((free C).obj I).right) =
      X.hom ≫ prod.lift (𝟙 X.right) (terminal.from X.right ≫ ((free C).obj I).hom)
    have h : terminal.from (⊤_ (Cᵒᵖ ⥤ SSet.{w})) = 𝟙 _ := terminal.hom_ext _ _
    rw [prod.comp_lift, prod.comp_lift, terminal.comp_from_assoc, terminal.comp_from_assoc, h,
      Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
  apply coprod.hom_ext
  · change freeInclusion C I ≫ parameterAxis X I ≫ productToCylinder X I =
      freeInclusion C I ≫ terminal.from ((free C).obj I).right ≫
        (parameterizedCylinder X I).hom
    rw [← Category.assoc, freeInclusion_parameterAxis, Category.assoc, productInl_toCylinder,
      intervalAxis_cylinderProductLeg, terminal.comp_from_assoc]
  · change ((free C).obj I).hom ≫ parameterAxis X I ≫ productToCylinder X I =
      ((free C).obj I).hom ≫ terminal.from ((free C).obj I).right ≫
        (parameterizedCylinder X I).hom
    rw [← Category.assoc, h₁, Category.assoc, productInr_toCylinder,
      terminal.comp_from_assoc, terminal.comp_from_assoc]

private def smashToCylinder : Under.smash X ((free C).obj I) ⟶ parameterizedCylinder X I :=
  Under.homMk (pushout.desc (productToCylinder X I) (parameterizedCylinder X I).hom (by
    apply coprod.hom_ext
    · simpa only [Under.axesToProduct, coprod.inl_desc_assoc, terminal.comp_from_assoc] using
        productInr_toCylinder X I
    · simpa only [Under.axesToProduct, coprod.inr_desc_assoc, terminal.comp_from_assoc] using
        parameterAxis_toCylinder X I))
    (pushout.inr_desc _ _ _)

private def cylinderToSmash : parameterizedCylinder X I ⟶ Under.smash X ((free C).obj I) :=
  Under.homMk (pushout.desc
    (freeParameterProductInclusion X I ≫ Under.toSmash X ((free C).obj I))
    (Under.smash X ((free C).obj I)).hom (by
      rw [← Category.assoc, ← freeInclusion_parameterAxis, Category.assoc]
      change freeInclusion C I ≫
        (prod.lift (terminal.from ((free C).obj I).right ≫ X.hom) (𝟙 _) ≫ _) = _
      rw [Under.rightAxis_toSmash, terminal.comp_from_assoc]))
    (pushout.inr_desc _ _ _)

@[reassoc]
private theorem toSmash_toCylinder :
    Under.toSmash X ((free C).obj I) ≫ (smashToCylinder X I).right = productToCylinder X I :=
  pushout.inl_desc _ _ _

@[reassoc]
private theorem productLeg_toSmash :
    cylinderProductLeg X I ≫ (cylinderToSmash X I).right =
      freeParameterProductInclusion X I ≫ Under.toSmash X ((free C).obj I) :=
  pushout.inl_desc _ _ _

/-- The actual pointed cylinder identifies with smashing with the freely pointed parameter. -/
@[no_expose]
def freeParameterSmashIso : Under.smash X ((free C).obj I) ≅ parameterizedCylinder X I where
  hom := smashToCylinder X I
  inv := cylinderToSmash X I
  hom_inv_id := by
    apply Under.smash_hom_ext
    simp only [Under.comp_right, Under.id_right, toSmash_toCylinder_assoc, Category.comp_id]
    apply productLegs_hom_ext X I
    · rw [productInl_toCylinder_assoc, productLeg_toSmash]
    · rw [productInr_toCylinder_assoc, Under.w, Under.leftAxis_toSmash]
  inv_hom_id := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change cylinderProductLeg X I ≫ (cylinderToSmash X I).right ≫ (smashToCylinder X I).right =
        cylinderProductLeg X I ≫ 𝟙 _
      rw [productLeg_toSmash_assoc, toSmash_toCylinder, productInl_toCylinder,
        Category.comp_id]
    · change (parameterizedCylinder X I).hom ≫ (cylinderToSmash X I).right ≫
        (smashToCylinder X I).right = (parameterizedCylinder X I).hom ≫ 𝟙 _
      rw [← Category.assoc, Under.w, Under.w, Category.comp_id]

/-- The comparison sends the actual product leg to the smash quotient. -/
@[reassoc]
theorem freeParameterSmashIso_inv_productLeg :
    cylinderProductLeg X I ≫ (freeParameterSmashIso X I).inv.right =
      freeParameterProductInclusion X I ≫ Under.toSmash X ((free C).obj I) :=
  productLeg_toSmash X I

/-- The comparison commutes with changing the parameter. -/
@[reassoc]
theorem freeParameterSmashIso_parameter {I' : Cᵒᵖ ⥤ SSet.{w}} (f : I ⟶ I') :
    Under.smashMap (𝟙 X) ((free C).map f) ≫ (freeParameterSmashIso X I').hom =
      (freeParameterSmashIso X I).hom ≫ parameterizedCylinderParameterMap I f X := by
  apply (cancel_epi (freeParameterSmashIso X I).inv).1
  have h : (freeParameterSmashIso X I).inv ≫ Under.smashMap (𝟙 X) ((free C).map f) =
      parameterizedCylinderParameterMap I f X ≫ (freeParameterSmashIso X I').inv := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change cylinderProductLeg X I ≫ ((freeParameterSmashIso X I).inv ≫
          Under.smashMap (𝟙 X) ((free C).map f)).right =
        cylinderProductLeg X I ≫ (parameterizedCylinderParameterMap I f X ≫
          (freeParameterSmashIso X I').inv).right
      rw [Under.comp_right, Under.comp_right, freeParameterSmashIso_inv_productLeg_assoc,
        Under.toSmash_smashMap, cylinderProductLeg_parameterizedCylinderParameterMap_assoc,
        freeParameterSmashIso_inv_productLeg, ← Category.assoc, ← Category.assoc]
      change (prod.map (𝟙 X.right) (freeInclusion C I) ≫
          prod.map (𝟙 X.right) ((free C).map f).right) ≫ _ =
        (prod.map (𝟙 X.right) f ≫ prod.map (𝟙 X.right) (freeInclusion C I')) ≫ _
      rw [prod.map_map, prod.map_map, freeInclusion_naturality]
    · exact (Under.w ((freeParameterSmashIso X I).inv ≫
        Under.smashMap (𝟙 X) ((free C).map f))).trans
        (Under.w (parameterizedCylinderParameterMap I f X ≫
          (freeParameterSmashIso X I').inv)).symm
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- The comparison commutes with the original pointed map in the base. -/
@[reassoc]
theorem freeParameterSmashIso_base {Y : PointedSimplicialPresheaf.{w} C} (g : X ⟶ Y) :
    Under.smashMap g (𝟙 ((free C).obj I)) ≫ (freeParameterSmashIso Y I).hom =
      (freeParameterSmashIso X I).hom ≫ parameterizedCylinderMap g I := by
  apply (cancel_epi (freeParameterSmashIso X I).inv).1
  have h : (freeParameterSmashIso X I).inv ≫ Under.smashMap g (𝟙 ((free C).obj I)) =
      parameterizedCylinderMap g I ≫ (freeParameterSmashIso Y I).inv := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change cylinderProductLeg X I ≫ ((freeParameterSmashIso X I).inv ≫
          Under.smashMap g (𝟙 ((free C).obj I))).right =
        cylinderProductLeg X I ≫ (parameterizedCylinderMap g I ≫
          (freeParameterSmashIso Y I).inv).right
      rw [Under.comp_right, Under.comp_right, freeParameterSmashIso_inv_productLeg_assoc,
        Under.toSmash_smashMap, cylinderProductLeg_parameterizedCylinderMap_assoc,
        freeParameterSmashIso_inv_productLeg, ← Category.assoc, ← Category.assoc]
      change (prod.map (𝟙 X.right) (freeInclusion C I) ≫
          prod.map g.right (𝟙 ((free C).obj I).right)) ≫ _ =
        (prod.map g.right (𝟙 I) ≫ prod.map (𝟙 Y.right) (freeInclusion C I)) ≫ _
      rw [prod.map_map, prod.map_map, Category.id_comp, Category.id_comp,
        Category.comp_id, Category.comp_id]
    · exact (Under.w ((freeParameterSmashIso X I).inv ≫
        Under.smashMap g (𝟙 ((free C).obj I)))).trans
        (Under.w (parameterizedCylinderMap g I ≫ (freeParameterSmashIso Y I).inv)).symm
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

end CategoryTheory.PointedSimplicialPresheaf
