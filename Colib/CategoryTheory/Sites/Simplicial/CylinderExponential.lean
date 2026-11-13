/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.UnderExponential
public import Colib.CategoryTheory.Sites.Simplicial.FreeParameterSmash

/-!
# The exponential adjunction for the pointed cylinder

Currying the product leg takes its collapsed basepoint axis to the
constant point of the exponential. This is the actual right adjoint
of the smash with the freely pointed parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]
  (I : Cᵒᵖ ⥤ SSet.{w})

private theorem prodMap_hom_eq (X : PointedSimplicialPresheaf.{w} C) :
    prod.map X.hom (𝟙 I) =
      (CategoryTheory.Limits.prod.leftUnitor I).hom ≫ intervalAxis X I := by
  apply prod.hom_ext
  · have ht : (prod.fst : (⊤_ _) ⨯ I ⟶ (⊤_ _)) = prod.snd ≫ terminal.from I :=
      terminal.hom_ext _ _
    simp [CategoryTheory.Limits.prod.leftUnitor, intervalAxis, ht]
  · simp [CategoryTheory.Limits.prod.leftUnitor, intervalAxis]

variable [MonoidalClosed (Cᵒᵖ ⥤ SSet.{w})]

private def cylinderCurry {X Y : PointedSimplicialPresheaf.{w} C}
    (f : parameterizedCylinder X I ⟶ Y) : X ⟶ Under.constantPointExponential I Y :=
  Under.homMk ((prodRightIhomAdjunction I).homEquiv X.right Y.right
    (cylinderProductLeg X I ≫ f.right)) (by
    let a := prodRightIhomAdjunction I
    change X.hom ≫ a.homEquiv _ _ _ = a.homEquiv _ _ _
    rw [← a.homEquiv_naturality_left]
    change a.homEquiv _ _ (prod.map X.hom (𝟙 I) ≫ _) = _
    rw [prodMap_hom_eq, Category.assoc, intervalAxis_cylinderProductLeg_assoc, Under.w f]
    exact congrArg (a.homEquiv (⊤_ _) Y.right)
      (terminal.comp_from_assoc (CategoryTheory.Limits.prod.leftUnitor I).hom Y.hom))

private def cylinderUncurry {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Under.constantPointExponential I Y) : parameterizedCylinder X I ⟶ Y := by
  let a := prodRightIhomAdjunction I
  let r : X.right ⟶ (ihom I).obj Y.right := f.right
  let m := (a.homEquiv X.right Y.right).symm r
  have hm : prod.map X.hom (𝟙 I) ≫ m = terminal.from ((⊤_ _) ⨯ I) ≫ Y.hom := by
    have h : X.hom ≫ r = a.homEquiv _ _ (terminal.from ((⊤_ _) ⨯ I) ≫ Y.hom) := Under.w f
    change (prod.functor.flip.obj I).map X.hom ≫ (a.homEquiv _ _).symm r = _
    rw [← a.homEquiv_naturality_left_symm, h]
    exact (a.homEquiv _ _).symm_apply_apply _
  have h : intervalAxis X I ≫ m = terminal.from I ≫ Y.hom := by
    rw [prodMap_hom_eq, Category.assoc] at hm
    apply (cancel_epi (CategoryTheory.Limits.prod.leftUnitor I).hom).1
    exact hm.trans (terminal.comp_from_assoc _ _).symm
  exact Under.homMk (pushout.desc m Y.hom h) (pushout.inr_desc _ _ _)

@[reassoc]
private theorem cylinderProductLeg_cylinderUncurry {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Under.constantPointExponential I Y) :
    cylinderProductLeg X I ≫ (cylinderUncurry I f).right =
      ((prodRightIhomAdjunction I).homEquiv X.right Y.right).symm f.right :=
  pushout.inl_desc _ _ _

/-- Transposing a map on the original cylinder uses its actual product leg. -/
@[no_expose]
def cylinderExponentialHomEquiv (X Y : PointedSimplicialPresheaf.{w} C) :
    (parameterizedCylinder X I ⟶ Y) ≃ (X ⟶ Under.constantPointExponential I Y) where
  toFun := cylinderCurry I
  invFun := cylinderUncurry I
  left_inv f := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change cylinderProductLeg X I ≫ (cylinderUncurry I (cylinderCurry I f)).right = _
      rw [cylinderProductLeg_cylinderUncurry]
      exact ((prodRightIhomAdjunction I).homEquiv _ _).symm_apply_apply _
    · exact (Under.w (cylinderUncurry I (cylinderCurry I f))).trans (Under.w f).symm
  right_inv f := by
    apply Under.UnderMorphism.ext
    change (prodRightIhomAdjunction I).homEquiv _ _
      (cylinderProductLeg X I ≫ (cylinderUncurry I f).right) = f.right
    rw [cylinderProductLeg_cylinderUncurry]
    exact ((prodRightIhomAdjunction I).homEquiv X.right Y.right).apply_symm_apply f.right

/-- Transposition commutes with the actual change of cylinder parameter. -/
theorem cylinderExponentialHomEquiv_parameter {K : Cᵒᵖ ⥤ SSet.{w}} (s : I ⟶ K)
    {X Y : PointedSimplicialPresheaf.{w} C} (f : parameterizedCylinder X K ⟶ Y) :
    cylinderExponentialHomEquiv I X Y (parameterizedCylinderParameterMap I s X ≫ f) =
      cylinderExponentialHomEquiv K X Y f ≫ Under.constantPointExponentialPre s Y := by
  apply Under.UnderMorphism.ext
  let a := cylinderProductLeg X K ≫ f.right
  change (prodRightIhomAdjunction I).homEquiv _ _
      (cylinderProductLeg X I ≫ (parameterizedCylinderParameterMap I s X).right ≫ f.right) =
    (prodRightIhomAdjunction K).homEquiv _ _ a ≫ (MonoidalClosed.pre s).app Y.right
  rw [cylinderProductLeg_parameterizedCylinderParameterMap_assoc, prodRightCurry_pre]

/-- The actual exponential with its constant point is right adjoint to
the original smash with the freely pointed parameter. -/
@[no_expose]
def freeParameterSmashAdjunction :
    Under.smashRightFunctor ((free C).obj I) ⊣ Under.constantPointExponentialFunctor I :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := (freeParameterSmashIso X I).homFromEquiv.trans
      (cylinderExponentialHomEquiv I X Y)
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      let g' : X ⟶ Under.constantPointExponential I Y := g
      have h : cylinderUncurry I (f ≫ g') =
          parameterizedCylinderMap f I ≫ cylinderUncurry I g' := by
        apply Under.UnderMorphism.ext
        apply pushout.hom_ext
        · change cylinderProductLeg X' I ≫ (cylinderUncurry I (f ≫ g')).right =
            cylinderProductLeg X' I ≫ (parameterizedCylinderMap f I).right ≫
              (cylinderUncurry I g').right
          rw [cylinderProductLeg_cylinderUncurry, cylinderProductLeg_parameterizedCylinderMap_assoc]
          let a := prodRightIhomAdjunction I
          let r : X.right ⟶ (ihom I).obj Y.right := g'.right
          change (a.homEquiv _ _).symm (f.right ≫ r) = _
          exact (a.homEquiv_naturality_left_symm f.right r).trans
            (congrArg (prod.map f.right (𝟙 I) ≫ ·)
              (cylinderProductLeg_cylinderUncurry I g').symm)
        · exact (Under.w (cylinderUncurry I (f ≫ g'))).trans
            (Under.w (parameterizedCylinderMap f I ≫ cylinderUncurry I g')).symm
      change (freeParameterSmashIso X' I).hom ≫ cylinderUncurry I (f ≫ g') =
        Under.smashMap f (𝟙 _) ≫ (freeParameterSmashIso X I).hom ≫ cylinderUncurry I g'
      exact (congrArg ((freeParameterSmashIso X' I).hom ≫ ·) h).trans
        (freeParameterSmashIso_base_assoc X' I f _).symm
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply Under.UnderMorphism.ext
      let m := cylinderProductLeg X I ≫ ((freeParameterSmashIso X I).inv ≫ f).right
      change (prodRightIhomAdjunction I).homEquiv _ _
          (cylinderProductLeg X I ≫ ((freeParameterSmashIso X I).inv ≫ f ≫ g).right) =
        (prodRightIhomAdjunction I).homEquiv _ _ m ≫ (ihom I).map g.right
      rw [← (prodRightIhomAdjunction I).homEquiv_naturality_right]
      apply congrArg ((prodRightIhomAdjunction I).homEquiv X.right Y'.right)
      dsimp only [m]
      have h : (freeParameterSmashIso X I).inv ≫ f ≫ g =
          ((freeParameterSmashIso X I).inv ≫ f) ≫ g := (Category.assoc _ _ _).symm
      exact (congrArg (fun p : parameterizedCylinder X I ⟶ Y' =>
        cylinderProductLeg X I ≫ p.right) h).trans
          (Category.assoc (cylinderProductLeg X I) _ _).symm }

/-- The chosen adjunction transposes a cylinder map using the original quotient comparison. -/
theorem freeParameterSmashAdjunction_homEquiv {X Y : PointedSimplicialPresheaf.{w} C}
    (f : parameterizedCylinder X I ⟶ Y) :
    (freeParameterSmashAdjunction I).homEquiv X Y ((freeParameterSmashIso X I).hom ≫ f) =
      cylinderExponentialHomEquiv I X Y f := by
  unfold freeParameterSmashAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change cylinderExponentialHomEquiv I X Y ((freeParameterSmashIso X I).inv ≫
    (freeParameterSmashIso X I).hom ≫ f) = _
  rw [Iso.inv_hom_id_assoc]

end CategoryTheory.PointedSimplicialPresheaf
