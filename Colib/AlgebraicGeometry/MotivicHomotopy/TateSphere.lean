/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Sites.Smooth.Torus
public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# The affine-line projection and the strict Tate quotient

The affine line is the native polynomial spectrum in the existing smooth site.
The torus and its point one are the existing Laurent-spectrum objects. Their
actual sections define pointed discrete Yoneda presheaves, and the original
Laurent open induces a pointed map. Its pushout along the collapse to the point
is the strict presheaf quotient `T = A¹ / (A¹ - 0)`.

The affine-line localization generators are the freely pointed Yoneda images of
the literal relative product projections. This file proves no weak-equivalence
or localization assertion. In particular, the comparison with the simplicial
suspension of `(G_m, 1)` still requires the cone roof of Morel--Voevodsky,
Section 3, Lemma 2.15; there is no asserted strict map from that suspension to
the constant quotient here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (R : CommRingCat.{u})

/-- The actual polynomial spectrum as a smooth separated finite-type object. -/
def affineLine : SmoothSite (Spec R) :=
  mk (polynomialProjection R)

@[simp]
theorem affineLine_left : (affineLine R).left = Spec (.of (Polynomial R)) := rfl

@[simp]
theorem affineLine_hom : (affineLine R).hom = polynomialProjection R := rfl

/-- The zero section in the existing smooth site. -/
def affineLineZero : base (Spec R) ⟶ affineLine R :=
  homMk (polynomialZeroSection R) (polynomialZeroSection_projection R)

/-- The point one in the existing smooth site. -/
def affineLineOne : base (Spec R) ⟶ affineLine R :=
  homMk (polynomialOneSection R) (polynomialOneSection_projection R)

@[simp]
theorem affineLineZero_left : (affineLineZero R).left = polynomialZeroSection R := rfl

@[simp]
theorem affineLineOne_left : (affineLineOne R).left = polynomialOneSection R := rfl

/-- The original Laurent open, regarded as a morphism of the actual smooth objects. -/
def torusToAffineLine : torus R ⟶ affineLine R :=
  homMk (laurentToPolynomial R) (laurentToPolynomial_projection R)

@[simp]
theorem torusToAffineLine_left :
    (torusToAffineLine R).left = laurentToPolynomial R := rfl

/-- The original Laurent inclusion preserves the selected point one. -/
@[reassoc (attr := simp)]
theorem torusOne_toAffineLine :
    torusOne R ≫ torusToAffineLine R = affineLineOne R :=
  MorphismProperty.Over.Hom.ext (laurentOneSection_toPolynomial R)

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.MotivicHomotopy

open Scheme Scheme.SmoothSite
open CategoryTheory.PointedSimplicialPresheaf

variable (R : CommRingCat.{u})

/-- An affine-line localization generator is the actual pointed representable projection. -/
def affineLineProjection (U : SmoothSite (Spec R)) :
    (PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).obj
        (product U (affineLine R)) ⟶
      (PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).obj U :=
  (PointedSimplicialPresheaf.yoneda (SmoothSite (Spec R))).map
    (productFst U (affineLine R))

/-- Forgetting the basepoint retains precisely the original discrete Yoneda projection. -/
theorem affineLineProjection_right (U : SmoothSite (Spec R)) :
    (affineLineProjection R U).right =
      coprod.map
        ((simplicialYoneda (SmoothSite (Spec R))).map (productFst U (affineLine R)))
        (𝟙 _) := rfl

/-- A section over the terminal base gives its actual global point on discrete Yoneda. -/
def representablePoint {X : SmoothSite (Spec R)} (x : base (Spec R) ⟶ X) :
    (⊤_ ((SmoothSite (Spec R))ᵒᵖ ⥤ SSet.{u})) ⟶
      (simplicialYoneda (SmoothSite (Spec R))).obj X where
  app U :=
    { app n := ↾fun _ ↦ (baseIsTerminal (Spec R)).from U.unop ≫ x
      naturality n m f := by
        apply ConcreteCategory.hom_ext
        intro z
        rfl }
  naturality U V f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    change (baseIsTerminal (Spec R)).from V.unop ≫ x =
      f.unop ≫ ((baseIsTerminal (Spec R)).from U.unop ≫ x)
    rw [← Category.assoc]
    congr 1
    exact (baseIsTerminal (Spec R)).hom_ext _ _

/-- The global point evaluates to the specified section after the actual map to the base. -/
@[simp]
theorem representablePoint_app_app {X : SmoothSite (Spec R)}
    (x : base (Spec R) ⟶ X) (U : (SmoothSite (Spec R))ᵒᵖ)
    (n : SimplexCategoryᵒᵖ)
    (z : (((⊤_ ((SmoothSite (Spec R))ᵒᵖ ⥤ SSet.{u})).obj U).obj n)) :
    ((representablePoint R x).app U).app n z =
      (baseIsTerminal (Spec R)).from U.unop ≫ x := rfl

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
  exact Category.assoc ((baseIsTerminal (Spec R)).from U.unop) x f

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
  pointedRepresentable R (torusOne R)

/-- The actual affine line, pointed at one so that the Laurent open is pointed. -/
def pointedAffineLine : PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) :=
  pointedRepresentable R (affineLineOne R)

/-- The original Laurent open as a map of the representables pointed at one. -/
def pointedLaurentOpen : pointedTorus R ⟶ pointedAffineLine R :=
  Under.homMk ((simplicialYoneda (SmoothSite (Spec R))).map (torusToAffineLine R)) (by
    change representablePoint R (torusOne R) ≫
        (simplicialYoneda (SmoothSite (Spec R))).map (torusToAffineLine R) =
      representablePoint R (affineLineOne R)
    rw [representablePoint_map, torusOne_toAffineLine])

/-- Every component of the pointed inclusion is postcomposition by the original open map. -/
@[simp]
theorem pointedLaurentOpen_app_app (U : (SmoothSite (Spec R))ᵒᵖ)
    (n : SimplexCategoryᵒᵖ) (f : U.unop ⟶ torus R) :
    (((pointedLaurentOpen R).right.app U).app n) f = f ≫ torusToAffineLine R := rfl

/-- The strict pointed presheaf quotient of the affine line by its Laurent open. -/
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
theorem tateSphere_isPushout :
    IsPushout (pointedLaurentOpen R)
      (toPoint (SmoothSite (Spec R)) (pointedTorus R))
      (toTateSphere R) (tateSpherePoint R) :=
  IsPushout.of_hasPushout _ _

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-0386"]
  AlgebraicGeometry.MotivicHomotopy.tateSphere
  AlgebraicGeometry.MotivicHomotopy.tateSphere_isPushout
attribute [colib_ref "MorelVoevodsky1999" "Section 3.2, Lemma 2.15, p. 111" "ingredient"
  "The actual pointed open-complement quotient before the suspension comparison"]
  AlgebraicGeometry.MotivicHomotopy.tateSphere
