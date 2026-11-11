/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
public import Colib.Util.References
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# The affine-line projection and the strict Tate quotient

The native affine line and torus define discrete pointed Yoneda presheaves.
The torus identity maps to the affine-line point one under the positive Laurent
open. The pushout that collapses the torus defines the Tate quotient in pointed
simplicial presheaves. The affine-line projection uses the native smooth-site
cylinder from `SmoothSite.Contraction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (R : CommRingCat.{u})

/-- The point one on the affine line is the image of the native torus identity. -/
def affineLineOne : base (Spec R) ⟶ additiveGroupObject (Spec R) :=
  torusOne (Spec R) ≫ multiplicativeGroupOpen (Spec R)

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.MotivicHomotopy

open Scheme Scheme.SmoothSite
open CategoryTheory.PointedSimplicialPresheaf

variable (R : CommRingCat.{u})

/-- An affine-line localization generator is the actual pointed representable projection. -/
def affineLineProjection (U : SmoothSite (Spec R)) :
    (PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).obj
        ((Contraction.affineLineCylinder (S := Spec R)).obj U) ⟶
      (PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).obj U :=
  (PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).map
    ((Contraction.projection (additiveGroupObject (Spec R))).app U)

/-- Forgetting the basepoint retains precisely the original discrete Yoneda projection. -/
theorem affineLineProjection_right (U : SmoothSite (Spec R)) :
    (affineLineProjection R U).right =
      coprod.map
        ((simplicialYoneda (SmoothSite (Spec R))).map
          ((Contraction.projection (additiveGroupObject (Spec R))).app U))
        (𝟙 _) := rfl

/-- A section over the terminal base gives its actual global point on discrete Yoneda. -/
def representablePoint {X : SmoothSite (Spec R)} (x : base (Spec R) ⟶ X) :
    (⊤_ ((SmoothSite (Spec R))ᵒᵖ ⥤ SSet.{u})) ⟶
      (simplicialYoneda (SmoothSite (Spec R))).obj X where
  app U :=
    { app n := ↾fun _ ↦ Contraction.toBase U.unop ≫ x
      naturality n m f := by
        apply ConcreteCategory.hom_ext
        intro z
        rfl }
  naturality U V f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    change Contraction.toBase V.unop ≫ x =
      f.unop ≫ (Contraction.toBase U.unop ≫ x)
    rw [← Category.assoc, Contraction.comp_toBase]

/-- The global point evaluates to the specified section after the actual map to the base. -/
@[simp]
theorem representablePoint_app_app {X : SmoothSite (Spec R)}
    (x : base (Spec R) ⟶ X) (U : (SmoothSite (Spec R))ᵒᵖ)
    (n : SimplexCategoryᵒᵖ)
    (z : (((⊤_ ((SmoothSite (Spec R))ᵒᵖ ⥤ SSet.{u})).obj U).obj n)) :
    ConcreteCategory.hom (Y := (U.unop ⟶ X)) (((representablePoint R x).app U).app n) z =
      Contraction.toBase U.unop ≫ x := rfl

/-- The actual representable point commutes with postcomposition of its section. -/
@[reassoc]
theorem representablePoint_map {X Y : SmoothSite (Spec R)}
    (x : base (Spec R) ⟶ X) (f : X ⟶ Y) :
    representablePoint R x ≫ (simplicialYoneda (SmoothSite (Spec R))).map f =
      representablePoint R (x ≫ f) := by
  apply NatTrans.ext
  funext U
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact Category.assoc (Contraction.toBase U.unop) x f

/-- A scheme with its given section, in the selected pointed simplicial presheaf category. -/
def pointedRepresentable {X : SmoothSite (Spec R)} (x : base (Spec R) ⟶ X) :
    PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) :=
  Under.mk (representablePoint R x)

@[simp]
theorem pointedRepresentable_right {X : SmoothSite (Spec R)}
    (x : base (Spec R) ⟶ X) :
    (pointedRepresentable R x).right =
      (simplicialYoneda (SmoothSite (Spec R))).obj X := rfl

/-- The existing Laurent torus, pointed by its actual identity section. -/
def pointedTorus : PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) :=
  pointedRepresentable R (torusOne (Spec R))

/-- The actual affine line, pointed at one so that the Laurent open is pointed. -/
def pointedAffineLine : PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) :=
  pointedRepresentable R (affineLineOne R)

/-- The original Laurent open as a map of the representables pointed at one. -/
def pointedLaurentOpen : pointedTorus R ⟶ pointedAffineLine R :=
  Under.homMk ((simplicialYoneda (SmoothSite (Spec R))).map (multiplicativeGroupOpen (Spec R))) (by
    change representablePoint R (torusOne (Spec R)) ≫
        (simplicialYoneda (SmoothSite (Spec R))).map (multiplicativeGroupOpen (Spec R)) =
      representablePoint R (affineLineOne R)
    exact representablePoint_map R (torusOne (Spec R)) (multiplicativeGroupOpen (Spec R)))

/-- Every component of the pointed inclusion is postcomposition by the original open map. -/
@[simp]
theorem pointedLaurentOpen_app_app (U : (SmoothSite (Spec R))ᵒᵖ)
    (n : SimplexCategoryᵒᵖ) (f : U.unop ⟶ multiplicativeGroupObject (Spec R)) :
    (((pointedLaurentOpen R).right.app U).app n) f = f ≫ multiplicativeGroupOpen (Spec R) := rfl

/-- The strict pointed presheaf quotient of the affine line by its Laurent open. -/
@[colib_tag "COL-1017",
  colib_ref "MorelVoevodsky1999" "Section 3.2, pp. 110–111, before Lemma 2.15" "adaptation"
    "The strict presheaf quotient associated to the pointed Nisnevich sheaf quotient"]
def tateSphere : PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) :=
  pushout (pointedLaurentOpen R)
    (toPoint (SmoothSite (Spec R)) (pointedTorus R))

/-- The actual quotient map from the affine line pointed at one. -/
def toTateSphere : pointedAffineLine R ⟶ tateSphere R :=
  pushout.inl _ _

/-- The point leg of the defining quotient pushout. -/
def tateSpherePoint : point (SmoothSite (Spec R)) ⟶ tateSphere R :=
  pushout.inr _ _

/-- The Laurent open is collapsed along the actual map to the one-point presheaf. -/
@[reassoc]
theorem tateSphere_condition :
    pointedLaurentOpen R ≫ toTateSphere R =
      toPoint (SmoothSite (Spec R)) (pointedTorus R) ≫ tateSpherePoint R :=
  pushout.condition

/-- The displayed affine-line quotient square is a strict pointed pushout. -/
@[colib_tag "COL-1017"]
theorem tateSphere_isPushout :
    IsPushout (pointedLaurentOpen R)
      (toPoint (SmoothSite (Spec R)) (pointedTorus R))
      (toTateSphere R) (tateSpherePoint R) :=
  IsPushout.of_hasPushout _ _

end AlgebraicGeometry.MotivicHomotopy
