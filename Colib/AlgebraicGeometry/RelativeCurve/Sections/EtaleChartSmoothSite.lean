/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChart
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Keeping the original marked etale chart over the original base

The field of a mark is not made into a smooth-site object. Only the actual affine
chart and its affine coordinate base are promoted, over the unchanged base S.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
variable {S : Scheme.{u}} (Y : SmoothSite S) [IsAffine Y.left]
  {A Z : Scheme.{u}} [IsAffine A] [IsAffine Z]
  (p : Z ⟶ Y.left) [Smooth p] (q : A ⟶ Z) [Etale q]

/-- The unchanged coordinate space, over the original base. -/
def coordinateSite : SmoothSite S := SmoothSite.mk (p ≫ Y.hom)

/-- The unchanged intersection chart, not a new etale neighborhood. -/
def chartSite : SmoothSite S := SmoothSite.mk (q ≫ p ≫ Y.hom)

/-- The original projection as an arrow of the original smooth site. -/
def projection : coordinateSite Y p ⟶ Y := homMk p rfl

/-- The original etale map as an arrow of the original smooth site. -/
def chart : chartSite Y p q ⟶ coordinateSite Y p := homMk q rfl

/-- A section of p is automatically over the original base; no extra compatibility. -/
def sectionMap (s : Y.left ⟶ Z) (hs : s ≫ p = 𝟙 Y.left) :
    Y ⟶ coordinateSite Y p :=
  homMk s (by
    change s ≫ (p ≫ Y.hom) = Y.hom
    exact (Category.assoc s p Y.hom).symm.trans
      ((congrArg (fun z => z ≫ Y.hom) hs).trans (Category.id_comp Y.hom)))

@[simp] theorem coordinateSite_left : (coordinateSite Y p).left = Z := rfl
@[simp] theorem chartSite_left : (chartSite Y p q).left = A := rfl
@[simp] theorem coordinateSite_hom : (coordinateSite Y p).hom = p ≫ Y.hom := rfl
@[simp] theorem chartSite_hom : (chartSite Y p q).hom = q ≫ p ≫ Y.hom := rfl
@[simp] theorem projection_left : (projection Y p).left = p := rfl
@[simp] theorem chart_left : (chart Y p q).left = q := rfl
@[simp] theorem section_left (s : Y.left ⟶ Z) (hs : s ≫ p = 𝟙 Y.left) :
    (sectionMap Y p s hs).left = s := rfl

/-- The actual section identity holds in the native smooth-site category. -/
theorem section_projection (s : Y.left ⟶ Z) (hs : s ≫ p = 𝟙 Y.left) :
    sectionMap Y p s hs ≫ projection Y p = 𝟙 Y :=
  MorphismProperty.Over.Hom.ext hs

/-- Native arrows preserve the actual field-valued scheme marking, including for
fields which are not themselves objects of the smooth site over S. -/
theorem marked_chart {Ω : Type u} [Field Ω]
    (s : Y.left ⟶ Z) (hs : s ≫ p = 𝟙 Y.left)
    (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Y.left)
    (hξ : ξ ≫ q = η ≫ s) :
    ξ ≫ (chart Y p q).left = η ≫ (sectionMap Y p s hs).left := hξ

/-- Promotion does not alter the actual pullback refinement. -/
theorem refinement_eq (s : Y.left ⟶ Z) (hs : s ≫ p = 𝟙 Y.left) :
    Scheme.EtaleChart.refinement (chart Y p q).left (projection Y p).left
      (sectionMap Y p s hs).left = Scheme.EtaleChart.refinement q p s := rfl

/-- A target map through the retained inclusion remains an arrow to the original
smooth-site target. The sole hypothesis is its original over-base equation. -/
def retainedTarget {U : Scheme.{u}} (T : SmoothSite S)
    (i : A ⟶ U) (f : U ⟶ T.left)
    (hf : (i ≫ f) ≫ T.hom = q ≫ p ≫ Y.hom) : chartSite Y p q ⟶ T :=
  homMk (i ≫ f) hf

@[simp] theorem retainedTarget_left {U : Scheme.{u}} (T : SmoothSite S)
    (i : A ⟶ U) (f : U ⟶ T.left)
    (hf : (i ≫ f) ≫ T.hom = q ≫ p ≫ Y.hom) :
    (retainedTarget Y p q T i f hf).left = i ≫ f := rfl

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
