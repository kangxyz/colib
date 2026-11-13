/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Colib.CategoryTheory.Limits.PointedSmashFunctor
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Smash products and pointed cylinders

Both orders of taking the pointed smash quotient and the parameterized
cylinder collapse the same two axes of the threefold product. The comparison
retains the actual cylinder projection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

set_option backward.isDefEq.respectTransparency false

section Products

variable {D : Type u} [Category.{v} D] [HasTerminal D]

private def constantTo (A : D) (Z : Under (⊤_ D)) : A ⟶ Z.right :=
  terminal.from A ≫ Z.hom

@[simp, reassoc]
private theorem comp_constantTo {A B : D} (f : A ⟶ B) (Z : Under (⊤_ D)) :
    f ≫ constantTo B Z = constantTo A Z := by
  simp [constantTo]

variable [HasBinaryProducts D]

private def leftAxis (A : D) (Y : Under (⊤_ D)) : A ⟶ A ⨯ Y.right :=
  prod.lift (𝟙 A) (constantTo A Y)

private def rightAxis (X : Under (⊤_ D)) (B : D) : B ⟶ X.right ⨯ B :=
  prod.lift (constantTo B X) (𝟙 B)

@[reassoc]
private theorem leftAxis_naturality {A B : D} (f : A ⟶ B) (Y : Under (⊤_ D)) :
    leftAxis A Y ≫ prod.map f (𝟙 _) = f ≫ leftAxis B Y := by
  apply prod.hom_ext <;> simp [leftAxis]

@[reassoc]
private theorem leftAxis_comp_point (X Y : Under (⊤_ D)) :
    X.hom ≫ leftAxis X.right Y =
      prod.lift (𝟙 (⊤_ D)) Y.hom ≫ prod.map X.hom (𝟙 _) := by
  have ht : terminal.from (⊤_ D) = 𝟙 _ := terminal.hom_ext _ _
  apply prod.hom_ext <;> simp [leftAxis, constantTo, ht]

private theorem rightAxis_factor (X : Under (⊤_ D)) (B : D) :
    rightAxis X B = prod.lift (terminal.from B) (𝟙 B) ≫ prod.map X.hom (𝟙 B) := by
  apply prod.hom_ext <;> simp [rightAxis, constantTo]

private def swapSecondThird (A B E : D) : (A ⨯ B) ⨯ E ≅ (A ⨯ E) ⨯ B where
  hom := prod.lift (prod.lift (prod.fst ≫ prod.fst) prod.snd) (prod.fst ≫ prod.snd)
  inv := prod.lift (prod.lift (prod.fst ≫ prod.fst) prod.snd) (prod.fst ≫ prod.snd)
  hom_inv_id := by
    apply prod.hom_ext
    · apply prod.hom_ext <;> simp
    · simp
  inv_hom_id := by
    apply prod.hom_ext
    · apply prod.hom_ext <;> simp
    · simp

@[reassoc]
private theorem leftAxis_swap (A B : D) (Y : Under (⊤_ D)) :
    leftAxis (A ⨯ B) Y ≫ (swapSecondThird A B Y.right).hom =
      prod.map (leftAxis A Y) (𝟙 B) := by
  apply prod.hom_ext
  · apply prod.hom_ext <;> simp [leftAxis, swapSecondThird]
  · simp [leftAxis, swapSecondThird]

@[reassoc]
private theorem rightAxis_swap (X : Under (⊤_ D)) (B E : D) :
    prod.map (rightAxis X B) (𝟙 E) ≫ (swapSecondThird X.right B E).hom =
      (prod.braiding B E).hom ≫ prod.map (rightAxis X E) (𝟙 B) := by
  apply prod.hom_ext
  · apply prod.hom_ext <;> simp [rightAxis, swapSecondThird, prod.braiding]
  · simp [rightAxis, swapSecondThird, prod.braiding]

variable [HasBinaryCoproducts D] [HasPushouts D]

@[simp, reassoc]
private theorem leftAxis_toSmash (X Y : Under (⊤_ D)) :
    leftAxis X.right Y ≫ Under.toSmash X Y = constantTo X.right (Under.smash X Y) :=
  Under.leftAxis_toSmash X Y

@[simp, reassoc]
private theorem rightAxis_toSmash (X Y : Under (⊤_ D)) :
    rightAxis X Y.right ≫ Under.toSmash X Y = constantTo Y.right (Under.smash X Y) :=
  Under.rightAxis_toSmash X Y

@[reassoc]
private theorem pointProduct_toSmash (X Y : Under (⊤_ D)) :
    prod.map X.hom (𝟙 Y.right) ≫ Under.toSmash X Y =
      constantTo ((⊤_ D) ⨯ Y.right) (Under.smash X Y) := by
  have h : prod.map X.hom (𝟙 Y.right) = prod.snd ≫ rightAxis X Y.right := by
    have ht : (prod.fst : (⊤_ D) ⨯ Y.right ⟶ ⊤_ D) =
        terminal.from _ := terminal.hom_ext _ _
    apply prod.hom_ext <;> simp [rightAxis, constantTo, ht]
  rw [h, Category.assoc, rightAxis_toSmash, comp_constantTo]

private def smashDesc {X Y Z : Under (⊤_ D)} (f : X.right ⨯ Y.right ⟶ Z.right)
    (h₁ : leftAxis X.right Y ≫ f = constantTo X.right Z)
    (h₂ : rightAxis X Y.right ≫ f = constantTo Y.right Z) : Under.smash X Y ⟶ Z :=
  Under.homMk (pushout.desc f Z.hom (by
    apply coprod.hom_ext
    · simpa [Under.axesToProduct, leftAxis, constantTo] using h₁
    · simpa [Under.axesToProduct, rightAxis, constantTo] using h₂))
    (pushout.inr_desc _ _ _)

@[simp, reassoc]
private theorem toSmash_smashDesc {X Y Z : Under (⊤_ D)} (f : X.right ⨯ Y.right ⟶ Z.right)
    (h₁ : leftAxis X.right Y ≫ f = constantTo X.right Z)
    (h₂ : rightAxis X Y.right ≫ f = constantTo Y.right Z) :
    Under.toSmash X Y ≫ (smashDesc f h₁ h₂).right = f :=
  pushout.inl_desc _ _ _

end Products

variable {C : Type u} [Category.{v} C]

private def productFlipIso (T : Cᵒᵖ ⥤ SSet.{w}) :
    prod.functor.obj T ≅ prod.functor.flip.obj T :=
  NatIso.ofComponents (fun A => prod.braiding T A) (by
    intro A B f
    exact braid_natural (𝟙 T) f)

private instance rightProductPreservesColimitsOfShape {K : Type} [SmallCategory K]
    (T : Cᵒᵖ ⥤ SSet.{w}) : PreservesColimitsOfShape K (prod.functor.flip.obj T) := by
  let : PreservesColimitsOfShape K (prod.functor.obj T) :=
    preservesColimitsOfShape_of_natIso (CartesianMonoidalCategory.tensorLeftIsoProd T)
  exact preservesColimitsOfShape_of_natIso (productFlipIso T)

private theorem rightProductPushout {A B D : Cᵒᵖ ⥤ SSet.{w}} (f : A ⟶ B) (g : A ⟶ D)
    (T : Cᵒᵖ ⥤ SSet.{w}) :
    IsPushout (prod.map f (𝟙 T)) (prod.map g (𝟙 T))
      (prod.map (pushout.inl f g) (𝟙 T)) (prod.map (pushout.inr f g) (𝟙 T)) :=
  (prod.functor.flip.obj T).map_isPushout (IsPushout.of_hasPushout f g)

private theorem productCoproduct_hom_ext (A B T : Cᵒᵖ ⥤ SSet.{w})
    {Z : Cᵒᵖ ⥤ SSet.{w}} {f g : (A ⨿ B) ⨯ T ⟶ Z}
    (h₁ : prod.map coprod.inl (𝟙 T) ≫ f = prod.map coprod.inl (𝟙 T) ≫ g)
    (h₂ : prod.map coprod.inr (𝟙 T) ≫ f = prod.map coprod.inr (𝟙 T) ≫ g) :
    f = g := by
  let F := prod.functor.flip.obj T
  let e := PreservesColimitPair.iso F A B
  apply (cancel_epi e.hom).1
  apply coprod.hom_ext
  · simp only [e, PreservesColimitPair.iso_hom, inl_coprodComparison_assoc]
    change prod.map coprod.inl (𝟙 T) ≫ f = prod.map coprod.inl (𝟙 T) ≫ g
    exact h₁
  · simp only [e, PreservesColimitPair.iso_hom, inr_coprodComparison_assoc]
    change prod.map coprod.inr (𝟙 T) ≫ f = prod.map coprod.inr (𝟙 T) ≫ g
    exact h₂

private abbrev cylinderInl (X : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w}) :
    X.right ⨯ I ⟶ (parameterizedCylinder X I).right :=
  pushout.inl (intervalAxis X I) (terminal.from I)

@[reassoc]
private theorem cylinderInl_projection (X : PointedSimplicialPresheaf.{w} C)
    (I : Cᵒᵖ ⥤ SSet.{w}) :
    cylinderInl X I ≫ (cylinderProjection X I).right = prod.fst :=
  pushout.inl_desc _ _ _

@[reassoc]
private theorem productConstant_cylinderInl (A : Cᵒᵖ ⥤ SSet.{w})
    (Z : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w}) :
    prod.map (constantTo A Z) (𝟙 I) ≫ cylinderInl Z I =
      constantTo (A ⨯ I) (parameterizedCylinder Z I) := by
  have h : prod.map (constantTo A Z) (𝟙 I) = prod.snd ≫ intervalAxis Z I := by
    apply prod.hom_ext <;> simp [constantTo, intervalAxis]
  rw [h, Category.assoc, pushout.condition, ← Category.assoc, terminal.comp_from]
  rfl

@[reassoc]
private theorem pointProduct_cylinderInl (Z : PointedSimplicialPresheaf.{w} C)
    (I : Cᵒᵖ ⥤ SSet.{w}) :
    prod.map Z.hom (𝟙 I) ≫ cylinderInl Z I =
      constantTo ((⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⨯ I) (parameterizedCylinder Z I) := by
  have ht : terminal.from (⊤_ (Cᵒᵖ ⥤ SSet.{w})) = 𝟙 _ := terminal.hom_ext _ _
  simpa only [constantTo, ht, Category.id_comp] using
    productConstant_cylinderInl (⊤_ (Cᵒᵖ ⥤ SSet.{w})) Z I

private abbrev smashCylinderProduct (X Y : PointedSimplicialPresheaf.{w} C)
    (I : Cᵒᵖ ⥤ SSet.{w}) : (X.right ⨯ I) ⨯ Y.right ⟶
      (Under.smash (parameterizedCylinder X I) Y).right :=
  prod.map (cylinderInl X I) (𝟙 Y.right) ≫ Under.toSmash (parameterizedCylinder X I) Y

private abbrev cylinderSmashProduct (X Y : PointedSimplicialPresheaf.{w} C)
    (I : Cᵒᵖ ⥤ SSet.{w}) : (X.right ⨯ Y.right) ⨯ I ⟶
      (parameterizedCylinder (Under.smash X Y) I).right :=
  prod.map (Under.toSmash X Y) (𝟙 I) ≫ cylinderInl (Under.smash X Y) I

private theorem smashCylinder_hom_ext {X Y Z : PointedSimplicialPresheaf.{w} C}
    {I : Cᵒᵖ ⥤ SSet.{w}} {f g : Under.smash (parameterizedCylinder X I) Y ⟶ Z}
    (h : smashCylinderProduct X Y I ≫ f.right = smashCylinderProduct X Y I ≫ g.right) :
    f = g := by
  apply Under.smash_hom_ext
  apply (rightProductPushout (intervalAxis X I) (terminal.from I) Y.right).hom_ext
  · simpa only [Category.assoc] using h
  · change prod.map (parameterizedCylinder X I).hom (𝟙 Y.right) ≫
        Under.toSmash (parameterizedCylinder X I) Y ≫ f.right =
      prod.map (parameterizedCylinder X I).hom (𝟙 Y.right) ≫
        Under.toSmash (parameterizedCylinder X I) Y ≫ g.right
    simp only [pointProduct_toSmash_assoc, constantTo, Category.assoc, Under.w]

private theorem cylinderSmash_hom_ext {X Y Z : PointedSimplicialPresheaf.{w} C}
    {I : Cᵒᵖ ⥤ SSet.{w}} {f g : parameterizedCylinder (Under.smash X Y) I ⟶ Z}
    (h : cylinderSmashProduct X Y I ≫ f.right = cylinderSmashProduct X Y I ≫ g.right) :
    f = g := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · apply (rightProductPushout (Under.axesToProduct X Y) (terminal.from _) I).hom_ext
    · change prod.map (Under.toSmash X Y) (𝟙 I) ≫
          cylinderInl (Under.smash X Y) I ≫ f.right =
        prod.map (Under.toSmash X Y) (𝟙 I) ≫
          cylinderInl (Under.smash X Y) I ≫ g.right
      simpa only [Category.assoc] using h
    · change prod.map (Under.smash X Y).hom (𝟙 I) ≫
          cylinderInl (Under.smash X Y) I ≫ f.right =
        prod.map (Under.smash X Y).hom (𝟙 I) ≫
          cylinderInl (Under.smash X Y) I ≫ g.right
      simp only [pointProduct_cylinderInl_assoc, constantTo, Category.assoc, Under.w]
  · exact (Under.w f).trans (Under.w g).symm

/-- A map out of the threefold product which is constant on the indicated axes
descends through the cylinder and then the smash quotient. -/
private def smashCylinderDesc {X Y Z : PointedSimplicialPresheaf.{w} C}
    {I : Cᵒᵖ ⥤ SSet.{w}} (f : (X.right ⨯ I) ⨯ Y.right ⟶ Z.right)
    (h₁ : prod.map (intervalAxis X I) (𝟙 Y.right) ≫ f = constantTo (I ⨯ Y.right) Z)
    (h₂ : leftAxis (X.right ⨯ I) Y ≫ f = constantTo (X.right ⨯ I) Z) :
    {g : Under.smash (parameterizedCylinder X I) Y ⟶ Z //
      smashCylinderProduct X Y I ≫ g.right = f} := by
  let hP := rightProductPushout (intervalAxis X I) (terminal.from I) Y.right
  let k := constantTo ((⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⨯ Y.right) Z
  have h : prod.map (intervalAxis X I) (𝟙 Y.right) ≫ f =
      prod.map (terminal.from I) (𝟙 Y.right) ≫ k :=
    h₁.trans (comp_constantTo _ _).symm
  let d := hP.desc f k h
  have hL : prod.map (cylinderInl X I) (𝟙 Y.right) ≫ d = f := hP.inl_desc f k h
  have hR : prod.map (parameterizedCylinder X I).hom (𝟙 Y.right) ≫ d = k :=
    hP.inr_desc f k h
  have hl : leftAxis (parameterizedCylinder X I).right Y ≫ d =
      constantTo (parameterizedCylinder X I).right Z := by
    apply pushout.hom_ext
    · change cylinderInl X I ≫ _ = cylinderInl X I ≫ _
      rw [← leftAxis_naturality_assoc, hL, h₂, comp_constantTo]
    · change (parameterizedCylinder X I).hom ≫ _ =
        (parameterizedCylinder X I).hom ≫ _
      rw [leftAxis_comp_point_assoc, hR, comp_constantTo, comp_constantTo]
  have hr : rightAxis (parameterizedCylinder X I) Y.right ≫ d = constantTo Y.right Z := by
    rw [rightAxis_factor, Category.assoc, hR, comp_constantTo]
  refine ⟨smashDesc d hl hr, ?_⟩
  rw [Category.assoc, toSmash_smashDesc, hL]

/-- The same two axes give the factorization through the smash quotient
followed by the cylinder. -/
private def cylinderSmashDesc {X Y Z : PointedSimplicialPresheaf.{w} C}
    {I : Cᵒᵖ ⥤ SSet.{w}} (f : (X.right ⨯ Y.right) ⨯ I ⟶ Z.right)
    (h₁ : prod.map (leftAxis X.right Y) (𝟙 I) ≫ f = constantTo (X.right ⨯ I) Z)
    (h₂ : prod.map (rightAxis X Y.right) (𝟙 I) ≫ f = constantTo (Y.right ⨯ I) Z) :
    {g : parameterizedCylinder (Under.smash X Y) I ⟶ Z //
      cylinderSmashProduct X Y I ≫ g.right = f} := by
  let hP := rightProductPushout (Under.axesToProduct X Y) (terminal.from _) I
  let k := constantTo ((⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⨯ I) Z
  have h : prod.map (Under.axesToProduct X Y) (𝟙 I) ≫ f =
      prod.map (terminal.from _) (𝟙 I) ≫ k := by
    rw [comp_constantTo]
    apply productCoproduct_hom_ext X.right Y.right I
    · rw [comp_constantTo, prod.map_map_assoc, Category.id_comp]
      have hAxis : coprod.inl ≫ Under.axesToProduct X Y = leftAxis X.right Y :=
        coprod.inl_desc _ _
      rwa [hAxis]
    · rw [comp_constantTo, prod.map_map_assoc, Category.id_comp]
      have hAxis : coprod.inr ≫ Under.axesToProduct X Y = rightAxis X Y.right :=
        coprod.inr_desc _ _
      rwa [hAxis]
  let d : (Under.smash X Y).right ⨯ I ⟶ Z.right := hP.desc f k h
  have hL : prod.map (Under.toSmash X Y) (𝟙 I) ≫ d = f := hP.inl_desc f k h
  have hR : prod.map (Under.smash X Y).hom (𝟙 I) ≫ d = k := hP.inr_desc f k h
  have hr : intervalAxis (Under.smash X Y) I ≫ d = terminal.from I ≫ Z.hom := by
    change rightAxis (Under.smash X Y) I ≫ d = constantTo I Z
    rw [rightAxis_factor, Category.assoc, hR, comp_constantTo]
  refine ⟨Under.homMk (pushout.desc d Z.hom hr) (pushout.inr_desc _ _ _), ?_⟩
  change (prod.map (Under.toSmash X Y) (𝟙 I) ≫ cylinderInl (Under.smash X Y) I) ≫
    pushout.desc d Z.hom hr = f
  rw [Category.assoc, pushout.inl_desc, hL]

private def smashCylinderToCylinderSmash (X Y : PointedSimplicialPresheaf.{w} C)
    (I : Cᵒᵖ ⥤ SSet.{w}) :
    {g : Under.smash (parameterizedCylinder X I) Y ⟶ parameterizedCylinder (Under.smash X Y) I //
      smashCylinderProduct X Y I ≫ g.right =
        (swapSecondThird X.right I Y.right).hom ≫ cylinderSmashProduct X Y I} :=
  smashCylinderDesc ((swapSecondThird X.right I Y.right).hom ≫ cylinderSmashProduct X Y I)
    (by
      change prod.map (rightAxis X I) (𝟙 Y.right) ≫ _ = _
      rw [rightAxis_swap_assoc]
      simp only [cylinderSmashProduct, prod.map_map_assoc, Category.id_comp,
        rightAxis_toSmash, productConstant_cylinderInl, comp_constantTo])
    (by
      rw [leftAxis_swap_assoc]
      simp only [cylinderSmashProduct, prod.map_map_assoc, Category.id_comp,
        leftAxis_toSmash, productConstant_cylinderInl])

private def cylinderSmashToSmashCylinder (X Y : PointedSimplicialPresheaf.{w} C)
    (I : Cᵒᵖ ⥤ SSet.{w}) :
    {g : parameterizedCylinder (Under.smash X Y) I ⟶ Under.smash (parameterizedCylinder X I) Y //
      cylinderSmashProduct X Y I ≫ g.right =
        (swapSecondThird X.right I Y.right).inv ≫ smashCylinderProduct X Y I} :=
  cylinderSmashDesc ((swapSecondThird X.right I Y.right).inv ≫ smashCylinderProduct X Y I)
    (by
      rw [← leftAxis_swap, Category.assoc, Iso.hom_inv_id_assoc]
      simp only [smashCylinderProduct, leftAxis_naturality_assoc, leftAxis_toSmash,
        comp_constantTo])
    (by
      change prod.map (rightAxis X Y.right) (𝟙 I) ≫
        (swapSecondThird X.right Y.right I).hom ≫ smashCylinderProduct X Y I = _
      rw [rightAxis_swap_assoc]
      change (prod.braiding Y.right I).hom ≫ prod.map (intervalAxis X I) (𝟙 Y.right) ≫
        prod.map (cylinderInl X I) (𝟙 Y.right) ≫ Under.toSmash _ _ = _
      have h : intervalAxis X I ≫ cylinderInl X I =
          terminal.from I ≫ (parameterizedCylinder X I).hom := pushout.condition
      have h' : prod.map (terminal.from I ≫ (parameterizedCylinder X I).hom) (𝟙 Y.right) =
          prod.map (terminal.from I) (𝟙 Y.right) ≫
            prod.map (parameterizedCylinder X I).hom (𝟙 Y.right) := by
        rw [prod.map_map, Category.id_comp]
      rw [prod.map_map_assoc, Category.id_comp, h, h']
      simp only [Category.assoc, pointProduct_toSmash, comp_constantTo])

/-- Taking the pointed cylinder commutes with smashing on the right. The
comparison is induced by the permutation of the actual product factors. -/
@[no_expose]
def smashCylinderIso (X Y : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w}) :
    Under.smash (parameterizedCylinder X I) Y ≅ parameterizedCylinder (Under.smash X Y) I where
  hom := (smashCylinderToCylinderSmash X Y I).val
  inv := (cylinderSmashToSmashCylinder X Y I).val
  hom_inv_id := by
    apply smashCylinder_hom_ext
    rw [Under.comp_right, ← Category.assoc, (smashCylinderToCylinderSmash X Y I).property,
      Category.assoc, (cylinderSmashToSmashCylinder X Y I).property, Iso.hom_inv_id_assoc,
      Under.id_right, Category.comp_id]
  inv_hom_id := by
    apply cylinderSmash_hom_ext
    rw [Under.comp_right, ← Category.assoc, (cylinderSmashToSmashCylinder X Y I).property,
      Category.assoc, (smashCylinderToCylinderSmash X Y I).property, Iso.inv_hom_id_assoc,
      Under.id_right, Category.comp_id]

/-- The comparison identifies the actual smashed cylinder projection with
the cylinder projection of the smash. -/
@[reassoc]
theorem smashCylinderIso_hom_projection (X Y : PointedSimplicialPresheaf.{w} C)
    (I : Cᵒᵖ ⥤ SSet.{w}) :
    (smashCylinderIso X Y I).hom ≫ cylinderProjection (Under.smash X Y) I =
      Under.smashMap (cylinderProjection X I) (𝟙 Y) := by
  apply smashCylinder_hom_ext
  rw [Under.comp_right, ← Category.assoc]
  change smashCylinderProduct X Y I ≫ (smashCylinderToCylinderSmash X Y I).val.right ≫ _ = _
  rw [← Category.assoc, (smashCylinderToCylinderSmash X Y I).property]
  have h : (swapSecondThird X.right I Y.right).hom ≫
        (prod.fst : (X.right ⨯ Y.right) ⨯ I ⟶ X.right ⨯ Y.right) =
      prod.map (prod.fst : X.right ⨯ I ⟶ X.right) (𝟙 Y.right) := by
    apply prod.hom_ext <;> simp [swapSecondThird]
  simp only [smashCylinderProduct, cylinderSmashProduct, Category.assoc, cylinderInl_projection,
    Under.toSmash_smashMap, Under.id_right, prod.map_map_assoc, Category.id_comp,
    prod.map_fst, reassoc_of% h]

/-- The cylinder comparison retains the section at every original
global point of the interval. -/
@[reassoc]
theorem smashMap_cylinderSection_smashCylinderIso_hom
    (X Y : PointedSimplicialPresheaf.{w} C) {I : Cᵒᵖ ⥤ SSet.{w}}
    (i : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ I) :
    Under.smashMap (cylinderSection X i) (𝟙 Y) ≫ (smashCylinderIso X Y I).hom =
      cylinderSection (Under.smash X Y) i := by
  let p : X.right ⟶ X.right ⨯ I :=
    prod.lift (𝟙 _) (terminal.from X.right ≫ i)
  let q := Under.toSmash X Y
  let e := (smashCylinderIso X Y I).hom
  let s : (Under.smash X Y).right ⟶ (Under.smash X Y).right ⨯ I :=
    prod.lift (𝟙 _) (terminal.from _ ≫ i)
  have hp : prod.map p (𝟙 Y.right) ≫ (swapSecondThird X.right I Y.right).hom ≫
      prod.map q (𝟙 I) = q ≫ s := by
    have hfst : prod.map p (𝟙 Y.right) ≫ (swapSecondThird X.right I Y.right).hom ≫
        (prod.fst : (X.right ⨯ Y.right) ⨯ I ⟶ X.right ⨯ Y.right) = 𝟙 _ := by
      apply prod.hom_ext <;> simp [swapSecondThird, p]
    apply prod.hom_ext
    · simpa [s, Category.assoc] using congrArg (· ≫ q) hfst
    · simp [p, q, s, swapSecondThird]
  have h : smashCylinderProduct X Y I ≫ e.right =
      (swapSecondThird X.right I Y.right).hom ≫ cylinderSmashProduct X Y I :=
    (smashCylinderToCylinderSmash X Y I).property
  apply Under.smash_hom_ext
  rw [Under.comp_right, ← Category.assoc, Under.toSmash_smashMap]
  change prod.map (p ≫ cylinderInl X I) (𝟙 Y.right) ≫
      Under.toSmash (parameterizedCylinder X I) Y ≫ e.right =
    q ≫ s ≫ cylinderInl (Under.smash X Y) I
  have hm : prod.map (p ≫ cylinderInl X I) (𝟙 Y.right) =
      prod.map p (𝟙 Y.right) ≫ prod.map (cylinderInl X I) (𝟙 Y.right) := by
    rw [prod.map_map, Category.id_comp]
  rw [hm, Category.assoc]
  change prod.map p (𝟙 Y.right) ≫ smashCylinderProduct X Y I ≫ e.right = _
  rw [h]
  exact (reassoc_of% hp) _

/-- The smash of a cylinder projection passes the same interval-local tests. -/
theorem intervalWeakEquivalences_smashRightFunctor_map_cylinderProjection
    (J : GrothendieckTopology C) (I : Cᵒᵖ ⥤ SSet.{w})
    (X Y : PointedSimplicialPresheaf.{w} C) :
    intervalWeakEquivalences C J I ((Under.smashRightFunctor Y).map (cylinderProjection X I)) := by
  intro L hL
  let Q := toStalkwiseHomotopyCategory C J
  change Function.Bijective (fun g : Q.obj (Under.smash X Y) ⟶ L ↦
    Q.map (Under.smashMap (cylinderProjection X I) (𝟙 Y)) ≫ g)
  let e := Q.mapIso (smashCylinderIso X Y I)
  let p := Q.map (cylinderProjection (Under.smash X Y) I)
  have h : Q.map (Under.smashMap (cylinderProjection X I) (𝟙 Y)) = e.hom ≫ p := by
    change Q.map (Under.smashMap (cylinderProjection X I) (𝟙 Y)) =
      Q.map (smashCylinderIso X Y I).hom ≫ Q.map (cylinderProjection (Under.smash X Y) I)
    rw [← Q.map_comp, smashCylinderIso_hom_projection]
  rw [h]
  let E := e.symm.homCongr (Iso.refl L)
  have hE (g : Q.obj (parameterizedCylinder (Under.smash X Y) I) ⟶ L) :
      E g = e.hom ≫ g := by
    simp only [E, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  have hb : Function.Bijective (fun g : Q.obj (Under.smash X Y) ⟶ L ↦ E (p ≫ g)) :=
    E.bijective.comp (hL (Under.smash X Y))
  simpa only [hE, Category.assoc] using hb

end CategoryTheory.PointedSimplicialPresheaf
