/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Cylinders of freely pointed simplicial presheaves

The product with the interval distributes over a disjoint basepoint. The
cylinder identifies with the freely pointed product and retains the
projection to the original presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- Swap the two presheaf product factors naturally in the varying factor. -/
private def productFlipIso (I : Cᵒᵖ ⥤ SSet.{w}) :
    prod.functor.obj I ≅ prod.functor.flip.obj I :=
  NatIso.ofComponents (fun A => prod.braiding I A) (by
    intro A B f
    exact braid_natural (𝟙 I) f)

local instance rightProductPreservesBinaryCoproducts (I : Cᵒᵖ ⥤ SSet.{w}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (prod.functor.flip.obj I) := by
  let : PreservesColimitsOfShape (Discrete WalkingPair) (prod.functor.obj I) :=
    preservesColimitsOfShape_of_natIso (CartesianMonoidalCategory.tensorLeftIsoProd I)
  exact preservesColimitsOfShape_of_natIso (productFlipIso I)

/-- Distribute the interval product over a freely adjoined basepoint, identifying
the product of the point and the interval with the interval itself. -/
private def freeProductDistrib (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (A ⨯ I) ⨿ I ≅ ((free C).obj A).right ⨯ I :=
  coprod.mapIso (Iso.refl _) (Limits.prod.leftUnitor I).symm ≪≫
    PreservesColimitPair.iso (prod.functor.flip.obj I) A (⊤_ _)

@[reassoc (attr := simp)]
private theorem freeProductDistrib_inl (A I : Cᵒᵖ ⥤ SSet.{w}) :
    coprod.inl ≫ (freeProductDistrib A I).hom = prod.map coprod.inl (𝟙 I) := by
  change coprod.inl ≫
    (coprod.map (𝟙 _) (Limits.prod.leftUnitor I).inv ≫
      coprodComparison (prod.functor.flip.obj I) A (⊤_ _)) = _
  rw [coprod.inl_map_assoc, Category.id_comp, inl_coprodComparison]
  rfl

@[reassoc (attr := simp)]
private theorem freeProductDistrib_inr (A I : Cᵒᵖ ⥤ SSet.{w}) :
    coprod.inr ≫ (freeProductDistrib A I).hom = intervalAxis ((free C).obj A) I := by
  change coprod.inr ≫
    (coprod.map (𝟙 _) (Limits.prod.leftUnitor I).inv ≫
      coprodComparison (prod.functor.flip.obj I) A (⊤_ _)) = _
  rw [coprod.inr_map_assoc, inr_coprodComparison]
  apply prod.hom_ext <;> simp [intervalAxis, Limits.prod.leftUnitor]

/-- Collapse the interval over the added basepoint and retain the other product summand. -/
private def freeCylinderCollapse (A I : Cᵒᵖ ⥤ SSet.{w}) :
    ((free C).obj A).right ⨯ I ⟶ ((free C).obj (A ⨯ I)).right :=
  (freeProductDistrib A I).inv ≫ coprod.map (𝟙 (A ⨯ I)) (terminal.from I)

@[reassoc (attr := simp)]
private theorem freeCylinderCollapse_inl (A I : Cᵒᵖ ⥤ SSet.{w}) :
    prod.map coprod.inl (𝟙 I) ≫ freeCylinderCollapse A I = coprod.inl := by
  rw [← freeProductDistrib_inl A I]
  simp only [freeCylinderCollapse, Category.assoc, Iso.hom_inv_id_assoc,
    coprod.inl_map, Category.id_comp]

@[reassoc (attr := simp)]
private theorem freeCylinderCollapse_axis (A I : Cᵒᵖ ⥤ SSet.{w}) :
    intervalAxis ((free C).obj A) I ≫ freeCylinderCollapse A I =
      terminal.from I ≫ coprod.inr := by
  rw [← freeProductDistrib_inr A I]
  simp only [freeCylinderCollapse, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_map]

/-- The quotient-induced pointed map from the cylinder of `A₊` to `(A × I)₊`. -/
private def freeCylinderToFree (A I : Cᵒᵖ ⥤ SSet.{w}) :
    parameterizedCylinder ((free C).obj A) I ⟶ (free C).obj (A ⨯ I) :=
  Under.homMk
    (pushout.desc (freeCylinderCollapse A I) coprod.inr (freeCylinderCollapse_axis A I))
    (pushout.inr_desc _ _ _)

@[simp]
private theorem freeCylinderToFree_right (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (freeCylinderToFree A I).right =
      pushout.desc (freeCylinderCollapse A I) coprod.inr (freeCylinderCollapse_axis A I) := rfl

/-- Map `(A × I)₊` into the cylinder using its product and basepoint inclusions. -/
private def freeToCylinder (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (free C).obj (A ⨯ I) ⟶ parameterizedCylinder ((free C).obj A) I :=
  Under.homMk
    (coprod.desc
      (prod.map coprod.inl (𝟙 I) ≫
        pushout.inl (intervalAxis ((free C).obj A) I) (terminal.from I))
      (pushout.inr (intervalAxis ((free C).obj A) I) (terminal.from I))) (by simp)

@[simp]
private theorem freeToCylinder_right (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (freeToCylinder A I).right =
      coprod.desc
        (prod.map coprod.inl (𝟙 I) ≫
          pushout.inl (intervalAxis ((free C).obj A) I) (terminal.from I))
        (pushout.inr (intervalAxis ((free C).obj A) I) (terminal.from I)) := rfl

private theorem freeCylinderCollapse_freeToCylinder (A I : Cᵒᵖ ⥤ SSet.{w}) :
    freeCylinderCollapse A I ≫ (freeToCylinder A I).right =
      pushout.inl (intervalAxis ((free C).obj A) I) (terminal.from I) := by
  apply (cancel_epi (freeProductDistrib A I).hom).1
  apply coprod.hom_ext
  · simp [freeCylinderCollapse, Category.assoc]
  · simpa [freeCylinderCollapse, Category.assoc] using
      (pushout.condition (f := intervalAxis ((free C).obj A) I)
        (g := terminal.from I)).symm

/-- Identify the pointed cylinder of `A₊` with `(A × I)₊` through the actual quotient maps. -/
@[no_expose]
def freeCylinderIso (A I : Cᵒᵖ ⥤ SSet.{w}) :
    parameterizedCylinder ((free C).obj A) I ≅ (free C).obj (A ⨯ I) where
  hom := freeCylinderToFree A I
  inv := freeToCylinder A I
  hom_inv_id := by
    apply Under.UnderMorphism.ext
    change (freeCylinderToFree A I).right ≫ (freeToCylinder A I).right = 𝟙 _
    apply pushout.hom_ext
    · simpa [Category.assoc] using
        freeCylinderCollapse_freeToCylinder A I
    · simp
  inv_hom_id := by
    apply Under.UnderMorphism.ext
    change (freeToCylinder A I).right ≫ (freeCylinderToFree A I).right = 𝟙 _
    apply coprod.hom_ext
    · simp
    · simp

private theorem freeCylinderCollapse_projection (A I : Cᵒᵖ ⥤ SSet.{w}) :
    freeCylinderCollapse A I ≫ ((free C).map (prod.fst : A ⨯ I ⟶ A)).right =
      prod.fst := by
  apply (cancel_epi (freeProductDistrib A I).hom).1
  apply coprod.hom_ext
  · simp [freeCylinderCollapse, Category.assoc]
  · simp [freeCylinderCollapse, Category.assoc, intervalAxis]

@[reassoc]
theorem freeCylinderIso_projection (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (freeCylinderIso A I).hom ≫ (free C).map (prod.fst : A ⨯ I ⟶ A) =
      cylinderProjection ((free C).obj A) I := by
  apply Under.UnderMorphism.ext
  change (freeCylinderToFree A I).right ≫ ((free C).map (prod.fst : A ⨯ I ⟶ A)).right =
    pushout.desc prod.fst coprod.inr _
  apply pushout.hom_ext
  · simpa [Category.assoc] using
      freeCylinderCollapse_projection A I
  · simp

private theorem intervalAxis_comp_map {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Y) (I : Cᵒᵖ ⥤ SSet.{w}) :
    intervalAxis X I ≫ prod.map f.right (𝟙 I) = (𝟙 I) ≫ intervalAxis Y I := by
  apply prod.hom_ext
  · simp [intervalAxis, Under.w]
  · simp [intervalAxis]

private def cylinderUnderlyingIso {X Y : PointedSimplicialPresheaf.{w} C}
    (e : X ≅ Y) (I : Cᵒᵖ ⥤ SSet.{w}) :
    (parameterizedCylinder X I).right ≅ (parameterizedCylinder Y I).right := by
  let p := prod.mapIso ((Under.forget _).mapIso e) (Iso.refl I)
  exact asIso (pushout.map (intervalAxis X I) (terminal.from I) (intervalAxis Y I)
    (terminal.from I) p.hom (𝟙 _) (𝟙 I) (intervalAxis_comp_map e.hom I) (by simp))

/-- A pointed isomorphism induces the corresponding isomorphism of cylinders. -/
@[no_expose]
def parameterizedCylinderIso {X Y : PointedSimplicialPresheaf.{w} C}
    (e : X ≅ Y) (I : Cᵒᵖ ⥤ SSet.{w}) :
    parameterizedCylinder X I ≅ parameterizedCylinder Y I :=
  Under.isoMk (cylinderUnderlyingIso e I) (by simp [cylinderUnderlyingIso])

/-- Transport of cylinders preserves the original projections. -/
@[reassoc]
theorem parameterizedCylinderIso_hom_projection {X Y : PointedSimplicialPresheaf.{w} C}
    (e : X ≅ Y) (I : Cᵒᵖ ⥤ SSet.{w}) :
    (parameterizedCylinderIso e I).hom ≫ cylinderProjection Y I =
      cylinderProjection X I ≫ e.hom := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · simp [parameterizedCylinderIso, cylinderUnderlyingIso, cylinderProjection]
  · simp [parameterizedCylinderIso, cylinderUnderlyingIso, cylinderProjection, Under.w]

end CategoryTheory.PointedSimplicialPresheaf
