/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProductInterchange
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The original Bass index square on arbitrary schemes

The positive and inverse charts define a genuine square functor on all schemes,
with no quasi-compactness hypotheses. Independent integer-base products commute
with this square by the original four swaps. The first component is identity;
the other components have the contravariant direction required by geometric K-theory.

Intended general owner: Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare.
The immediate consumer is the finite Bass seed interchange, not a tower construction.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

/-- The original polynomial product, now on every scheme. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:35"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def polynomial : Scheme.{u} ⥤ Scheme.{u} :=
  baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))

/-- The original Laurent product on every scheme. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:39"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def laurent : Scheme.{u} ⥤ Scheme.{u} :=
  baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))

/-- The actual positive coordinate chart. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:43"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def plus : laurent.{u} ⟶ polynomial.{u} :=
  baseProductTransformation _ _ (laurentToPolynomial (.of (ULift.{u} ℤ)))
    (laurentToPolynomial_projection (.of (ULift.{u} ℤ)))

/-- The actual inverse coordinate chart. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:48"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def minus : laurent.{u} ⟶ polynomial.{u} :=
  baseProductTransformation _ _ (laurentMinus (.of (ULift.{u} ℤ)))
    (laurentMinus_projection (.of (ULift.{u} ℤ)))

/-- The original projection from the polynomial product. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:53"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def projection : polynomial.{u} ⟶ 𝟭 _ := baseProductProjection _

/-- Both charts have exactly the same original projection to the base. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:56"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem chart_projection (X : Scheme.{u}) :
    plus.app X ≫ projection.app X = minus.app X ≫ projection.app X := by
  change (baseProductTransformation _ _ _ _).app X ≫ (baseProductProjection _).app X =
    (baseProductTransformation _ _ _ _).app X ≫ (baseProductProjection _).app X
  rw [baseProductTransformation_projection, baseProductTransformation_projection]

/-- The original four-corner square in the opposite scheme category. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:63"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def square (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow Scheme.{u}ᵒᵖ) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk (projection.app X.unop).op)
    (g := Arrow.mk (minus.app X.unop).op)
    (projection.app X.unop).op (plus.app X.unop).op
    (Quiver.Hom.unop_inj (chart_projection X.unop).symm))

/-- Every original scheme morphism acts on all four corners. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:70"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def squareMap {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) : square X ⟶ square Y :=
  Arrow.homMk
    (Arrow.homMk f (polynomial.map f.unop).op
      (Quiver.Hom.unop_inj (projection.naturality f.unop).symm))
    (Arrow.homMk (polynomial.map f.unop).op (laurent.map f.unop).op
      (Quiver.Hom.unop_inj (minus.naturality f.unop).symm)) (by
        apply Arrow.hom_ext
        · exact Quiver.Hom.unop_inj (projection.naturality f.unop).symm
        · exact Quiver.Hom.unop_inj (plus.naturality f.unop).symm)

/-- The original Bass evaluation square is strictly natural on arbitrary schemes. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:81"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def squareFunctor : Scheme.{u}ᵒᵖ ⥤ Arrow (Arrow Scheme.{u}ᵒᵖ) where
  obj := square
  map := squareMap
  map_id X := by
    apply Arrow.hom_ext <;> apply Arrow.hom_ext
    · rfl
    · simp [squareMap, square]
    · simp [squareMap, square]
    · simp [squareMap, square]
  map_comp f g := by
    apply Arrow.hom_ext <;> apply Arrow.hom_ext
    · rfl
    · simp [squareMap, square]
    · simp [squareMap, square]
    · simp [squareMap, square]

variable {T : Scheme.{u}} (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))

/-- The positive chart retains the whole original independent-variable swap square. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:100"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem swap_plus (X : Scheme.{u}) :
    (baseProductFunctor q).map (plus.app X) ≫
      (baseProductSwapIso (polynomialProjection (.of (ULift.{u} ℤ))) q).hom.app X =
    (baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).hom.app X ≫
      plus.app ((baseProductFunctor q).obj X) :=
  baseProductSwapIso_transformation_first _ _ q _ _ X

/-- The inverted chart retains the same literal independent-variable square. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:108"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem swap_minus (X : Scheme.{u}) :
    (baseProductFunctor q).map (minus.app X) ≫
      (baseProductSwapIso (polynomialProjection (.of (ULift.{u} ℤ))) q).hom.app X =
    (baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).hom.app X ≫
      minus.app ((baseProductFunctor q).obj X) :=
  baseProductSwapIso_transformation_first _ _ q _ _ X

/-- The actual four-corner index isomorphism, with the original positive and inverse charts. -/
@[colib_tag "COL-0532", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:116"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def squareIso (X : Scheme.{u}ᵒᵖ) :
    square ((baseProductFunctor q).op.obj X) ≅
      (baseProductFunctor q).op.mapArrow.mapArrow.obj (square X) :=
  Arrow.isoMk
    (Arrow.isoMk (Iso.refl _) ((baseProductSwapIso
      (polynomialProjection (.of (ULift.{u} ℤ))) q).app X.unop).op (by
        apply Quiver.Hom.unop_inj
        simpa [square, projection] using (baseProductSwapIso_projection_first
          (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).symm))
    (Arrow.isoMk ((baseProductSwapIso
      (polynomialProjection (.of (ULift.{u} ℤ))) q).app X.unop).op
      ((baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).app X.unop).op
      (Quiver.Hom.unop_inj (swap_minus q X.unop))) (by
        apply Arrow.hom_ext
        · apply Quiver.Hom.unop_inj
          simpa [square, projection] using (baseProductSwapIso_projection_first
            (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).symm
        · exact Quiver.Hom.unop_inj (swap_plus q X.unop))

/-- The original base corner is fixed literally. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:136"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_hom_base (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.left.left = 𝟙 ((baseProductFunctor q).op.obj X) := rfl

/-- The polynomial component has precisely the original swap's contravariant direction. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:140"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_hom_polynomial (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.left.right =
      (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op := rfl

/-- The Laurent corner retains the original, rather than an abstractly chosen, swap. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:145"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_hom_laurent (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.right.right =
      (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ))) q X.unop).op := rfl

/-- The four-corner swap commutes with every original base-scheme morphism. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:150"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    squareFunctor.map ((baseProductFunctor q).op.map f) ≫ (squareIso q Y).hom =
      (squareIso q X).hom ≫ (baseProductFunctor q).op.mapArrow.mapArrow.map
        (squareFunctor.map f) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · simp [squareIso, squareFunctor, squareMap]
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm

/-- Actual natural interchange between product-before-square and square-before-product. -/
@[colib_tag "COL-0532", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquare.lean:161"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def interchange : (baseProductFunctor q).op ⋙ squareFunctor ≅
    squareFunctor ⋙ (baseProductFunctor q).op.mapArrow.mapArrow :=
  NatIso.ofComponents (squareIso q) (squareIso_naturality q)

end AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

