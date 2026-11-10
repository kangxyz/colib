/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSphere
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# The actual affine line in interval localization

The interval is the unpointed discrete Yoneda presheaf of the native affine line,
and the topology is the existing Nisnevich topology on the smooth site. The
formal interval localization is the selected stalkwise construction.

Product distributes over the freely adjoined basepoint. Collapsing its interval
axis therefore identifies the cylinder on `U₊` with `(U × A¹)₊`. The comparison
retains the actual relative product projection. Consequently that projection is
inverted in this interval localization.

This does not assert enough points, a local model structure, or an equivalence
with the Morel--Voevodsky motivic homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PointedSimplicialPresheaf

set_option backward.isDefEq.respectTransparency false

universe w v u u'

namespace AlgebraicGeometry.MotivicHomotopy

section PresheafCylinder

variable {C : Type u'} [Category.{v} C]

/-- Swap the two presheaf product factors naturally in the varying factor. -/
def productFlipIso (I : Cᵒᵖ ⥤ SSet.{w}) :
    prod.functor.obj I ≅ prod.functor.flip.obj I :=
  NatIso.ofComponents (fun A => prod.braiding I A) (by
    intro A B f
    exact braid_natural (𝟙 I) f)

instance rightProductPreservesBinaryCoproducts (I : Cᵒᵖ ⥤ SSet.{w}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (prod.functor.flip.obj I) := by
  let : PreservesColimitsOfShape (Discrete WalkingPair) (prod.functor.obj I) :=
    preservesColimitsOfShape_of_natIso (CartesianMonoidalCategory.tensorLeftIsoProd I)
  exact preservesColimitsOfShape_of_natIso (productFlipIso I)

/-- Distribute the interval product over a freely adjoined basepoint, identifying
the product of the point and the interval with the interval itself. -/
def freeProductDistrib (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (A ⨯ I) ⨿ I ≅ ((free C).obj A).right ⨯ I :=
  coprod.mapIso (Iso.refl _) (prod.leftUnitor I).symm ≪≫
    PreservesColimitPair.iso (prod.functor.flip.obj I) A (⊤_ _)

@[reassoc (attr := simp)]
theorem freeProductDistrib_inl (A I : Cᵒᵖ ⥤ SSet.{w}) :
    coprod.inl ≫ (freeProductDistrib A I).hom = prod.map coprod.inl (𝟙 I) := by
  change coprod.inl ≫
    (coprod.map (𝟙 _) (Limits.prod.leftUnitor I).inv ≫
      coprodComparison (prod.functor.flip.obj I) A (⊤_ _)) = _
  rw [coprod.inl_map_assoc, Category.id_comp, inl_coprodComparison]
  rfl

@[reassoc (attr := simp)]
theorem freeProductDistrib_inr (A I : Cᵒᵖ ⥤ SSet.{w}) :
    coprod.inr ≫ (freeProductDistrib A I).hom = intervalAxis ((free C).obj A) I := by
  change coprod.inr ≫
    (coprod.map (𝟙 _) (Limits.prod.leftUnitor I).inv ≫
      coprodComparison (prod.functor.flip.obj I) A (⊤_ _)) = _
  rw [coprod.inr_map_assoc, inr_coprodComparison]
  apply prod.hom_ext <;> simp [intervalAxis, Limits.prod.leftUnitor]

/-- Collapse the interval over the added basepoint and retain the other product summand. -/
def freeCylinderCollapse (A I : Cᵒᵖ ⥤ SSet.{w}) :
    ((free C).obj A).right ⨯ I ⟶ ((free C).obj (A ⨯ I)).right :=
  (freeProductDistrib A I).inv ≫ coprod.map (𝟙 (A ⨯ I)) (terminal.from I)

@[reassoc (attr := simp)]
theorem freeCylinderCollapse_inl (A I : Cᵒᵖ ⥤ SSet.{w}) :
    prod.map coprod.inl (𝟙 I) ≫ freeCylinderCollapse A I = coprod.inl := by
  rw [← freeProductDistrib_inl A I]
  simp only [freeCylinderCollapse, Category.assoc, Iso.hom_inv_id_assoc,
    coprod.inl_map, Category.id_comp]

@[reassoc (attr := simp)]
theorem freeCylinderCollapse_axis (A I : Cᵒᵖ ⥤ SSet.{w}) :
    intervalAxis ((free C).obj A) I ≫ freeCylinderCollapse A I =
      terminal.from I ≫ coprod.inr := by
  rw [← freeProductDistrib_inr A I]
  simp only [freeCylinderCollapse, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_map]

/-- The quotient-induced pointed map from the cylinder of `A₊` to `(A × I)₊`. -/
def freeCylinderToFree (A I : Cᵒᵖ ⥤ SSet.{w}) :
    parameterizedCylinder ((free C).obj A) I ⟶ (free C).obj (A ⨯ I) :=
  Under.homMk
    (pushout.desc (freeCylinderCollapse A I) coprod.inr (freeCylinderCollapse_axis A I))
    (pushout.inr_desc _ _ _)

@[simp]
theorem freeCylinderToFree_right (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (freeCylinderToFree A I).right =
      pushout.desc (freeCylinderCollapse A I) coprod.inr (freeCylinderCollapse_axis A I) := rfl

/-- Map `(A × I)₊` into the cylinder using its product and basepoint inclusions. -/
def freeToCylinder (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (free C).obj (A ⨯ I) ⟶ parameterizedCylinder ((free C).obj A) I :=
  Under.homMk
    (coprod.desc
      (prod.map coprod.inl (𝟙 I) ≫
        pushout.inl (intervalAxis ((free C).obj A) I) (terminal.from I))
      (pushout.inr (intervalAxis ((free C).obj A) I) (terminal.from I))) (by simp)

@[simp]
theorem freeToCylinder_right (A I : Cᵒᵖ ⥤ SSet.{w}) :
    (freeToCylinder A I).right =
      coprod.desc
        (prod.map coprod.inl (𝟙 I) ≫
          pushout.inl (intervalAxis ((free C).obj A) I) (terminal.from I))
        (pushout.inr (intervalAxis ((free C).obj A) I) (terminal.from I)) := rfl

theorem freeCylinderCollapse_freeToCylinder (A I : Cᵒᵖ ⥤ SSet.{w}) :
    freeCylinderCollapse A I ≫ (freeToCylinder A I).right =
      pushout.inl (intervalAxis ((free C).obj A) I) (terminal.from I) := by
  apply (cancel_epi (freeProductDistrib A I).hom).1
  apply coprod.hom_ext
  · simp [freeCylinderCollapse, Category.assoc]
  · simpa [freeCylinderCollapse, Category.assoc] using
      (pushout.condition (f := intervalAxis ((free C).obj A) I)
        (g := terminal.from I)).symm

/-- Identify the pointed cylinder of `A₊` with `(A × I)₊` through the actual quotient maps. -/
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

theorem freeCylinderCollapse_projection (A I : Cᵒᵖ ⥤ SSet.{w}) :
    freeCylinderCollapse A I ≫ ((free C).map (prod.fst : A ⨯ I ⟶ A)).right =
      prod.fst := by
  apply (cancel_epi (freeProductDistrib A I).hom).1
  apply coprod.hom_ext
  · simp [freeCylinderCollapse, Category.assoc]
  · simp [freeCylinderCollapse, Category.assoc, intervalAxis]

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

end PresheafCylinder

open Scheme Scheme.SmoothSite

variable (R : CommRingCat.{u})

/-- The unpointed affine-line parameter is the actual discrete Yoneda presheaf. -/
abbrev affineLineParameter : (SmoothSite (Spec R))ᵒᵖ ⥤ SSet.{u} :=
  (simplicialYoneda (SmoothSite (Spec R))).obj (affineLine R)

/-- The selected interval localization for the actual smooth Nisnevich site and affine line. -/
abbrev AffineLineHomotopyCategory :=
  IntervalHomotopyCategory (SmoothSite (Spec R)) (nisnevichTopology (Spec R))
    (affineLineParameter R)

/-- The canonical functor to that formal affine-line interval localization. -/
abbrev toAffineLineHomotopyCategory :
    PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) ⥤ AffineLineHomotopyCategory R :=
  toIntervalHomotopyCategory (SmoothSite (Spec R)) (nisnevichTopology (Spec R))
    (affineLineParameter R)

instance simplicialYonedaPreservesPair (U V : SmoothSite (Spec R)) :
    PreservesLimit (pair U V) (simplicialYoneda (SmoothSite (Spec R))) := by
  dsimp [simplicialYoneda]
  infer_instance

/-- Discrete Yoneda carries the actual relative scheme product to the native presheaf product. -/
def simplicialYonedaProductIso (U V : SmoothSite (Spec R)) :
    (simplicialYoneda (SmoothSite (Spec R))).obj (product U V) ≅
      (simplicialYoneda (SmoothSite (Spec R))).obj U ⨯
        (simplicialYoneda (SmoothSite (Spec R))).obj V :=
  (simplicialYoneda (SmoothSite (Spec R))).mapIso (categoricalProductIso U V).symm ≪≫
    PreservesLimitPair.iso (simplicialYoneda (SmoothSite (Spec R))) U V

/-- The product comparison retains the first actual scheme projection. -/
@[reassoc (attr := simp)]
theorem simplicialYonedaProductIso_hom_fst (U V : SmoothSite (Spec R)) :
    (simplicialYonedaProductIso R U V).hom ≫ prod.fst =
      (simplicialYoneda (SmoothSite (Spec R))).map (productFst U V) := by
  simp only [simplicialYonedaProductIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← Functor.map_comp,
    categoricalProductIso_inv_fst]

@[reassoc (attr := simp)]
theorem simplicialYonedaProductIso_inv_fst (U V : SmoothSite (Spec R)) :
    (simplicialYonedaProductIso R U V).inv ≫
        (simplicialYoneda (SmoothSite (Spec R))).map (productFst U V) = prod.fst := by
  rw [← simplicialYonedaProductIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The pointed affine-line cylinder on `U₊` is the pointed representable of the actual product. -/
def affineLineCylinderIso (U : SmoothSite (Spec R)) :
    parameterizedCylinder
        ((PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).obj U)
        (affineLineParameter R) ≅
      (PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).obj
        (product U (affineLine R)) :=
  freeCylinderIso ((simplicialYoneda (SmoothSite (Spec R))).obj U) (affineLineParameter R) ≪≫
    (free (SmoothSite (Spec R))).mapIso (simplicialYonedaProductIso R U (affineLine R)).symm

/-- The cylinder comparison identifies the actual projection, not just its endpoints. -/
@[reassoc]
theorem affineLineCylinderIso_hom_projection (U : SmoothSite (Spec R)) :
    (affineLineCylinderIso R U).hom ≫ affineLineProjection R U =
      cylinderProjection
        ((PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).obj U)
        (affineLineParameter R) := by
  change ((freeCylinderIso _ _).hom ≫
      (free (SmoothSite (Spec R))).map (simplicialYonedaProductIso R U (affineLine R)).inv) ≫
      (free (SmoothSite (Spec R))).map
        ((simplicialYoneda (SmoothSite (Spec R))).map (productFst U (affineLine R))) = _
  rw [Category.assoc, ← Functor.map_comp, simplicialYonedaProductIso_inv_fst]
  exact freeCylinderIso_projection _ _

/-- The actual affine-line projection is inverted in the selected interval localization. -/
theorem isIso_toAffineLineHomotopyCategory_map_projection (U : SmoothSite (Spec R)) :
    IsIso ((toAffineLineHomotopyCategory R).map (affineLineProjection R U)) := by
  have h : IsIso ((toAffineLineHomotopyCategory R).map (affineLineCylinderIso R U).hom ≫
      (toAffineLineHomotopyCategory R).map (affineLineProjection R U)) := by
    rw [← Functor.map_comp, affineLineCylinderIso_hom_projection]
    exact isIso_toIntervalHomotopyCategory_map_cylinderProjection _ _ _ _
  exact IsIso.of_isIso_comp_left
    ((toAffineLineHomotopyCategory R).map (affineLineCylinderIso R U).hom)
    ((toAffineLineHomotopyCategory R).map (affineLineProjection R U))

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-0390"]
  AlgebraicGeometry.MotivicHomotopy.affineLineCylinderIso
  AlgebraicGeometry.MotivicHomotopy.affineLineCylinderIso_hom_projection
  AlgebraicGeometry.MotivicHomotopy.isIso_toAffineLineHomotopyCategory_map_projection
