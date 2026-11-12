/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactIntegerBaseProducts
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProperties

/-!
# Quasi-compact integer-base products and chart maps

Source: `Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean` at
revision `2c34f185fa859e862661f939cd216b07bcccfb26`.
The original maps and proofs use the existing native full category of quasi-compact schemes.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
open AlgebraicGeometry.Scheme.Products
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative


/-- The actual relative affine line X × Spec(Z[t]). -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:39"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def polynomialFunctor : QuasiCompactSchemes.{u} ⥤ QuasiCompactSchemes.{u} :=
  qcBaseProductFunctor (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))

/-- The actual relative Laurent scheme X × Spec(Z[t,t⁻¹]). -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:43"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def laurentFunctor : QuasiCompactSchemes.{u} ⥤ QuasiCompactSchemes.{u} :=
  qcBaseProductFunctor (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ)))

/-- The original plus-coordinate open chart, base changed over the actual integral base. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:47"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def plus : laurentFunctor.{u} ⟶ polynomialFunctor.{u} :=
  qcBaseProductTransformation _ _ (PolynomialLaurent.laurentToPolynomial (CommRingCat.of
    (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ)))

/-- The original inverse-coordinate open chart, with no choice of local coordinates on X. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:52"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def minus : laurentFunctor.{u} ⟶ polynomialFunctor.{u} :=
  qcBaseProductTransformation _ _ (PolynomialLaurent.laurentMinus (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ)))

@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:56"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
instance instIsOpenImmersionPlus (X : QuasiCompactSchemes.{u}) : IsOpenImmersion (plus.app X).hom :=
  by
  exact instIsOpenImmersionBaseProductTransformation _ _ _
    (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ))) X.obj

@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:61"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
instance instIsOpenImmersionMinus (X : QuasiCompactSchemes.{u}) : IsOpenImmersion (minus.app X).hom
  :=
  by
  exact instIsOpenImmersionBaseProductTransformation _ _ _
    (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ))) X.obj

/-- The original relative affine-line projection. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:68"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def polynomialProjection : polynomialFunctor.{u} ⟶ 𝟭 _ where
  app X := ⟨(baseProductProjection _).app X.obj⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (baseProductProjection _).naturality f.hom

/-- The original relative Laurent projection. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:75"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def laurentProjection : laurentFunctor.{u} ⟶ 𝟭 _ where
  app X := ⟨(baseProductProjection _).app X.obj⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (baseProductProjection _).naturality f.hom

@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:81"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
instance instFlatPolynomialProjection (X : QuasiCompactSchemes.{u}) :
    Flat (polynomialProjection.app X).hom := by
  change Flat (pullback.fst (specULiftZIsTerminal.from X.obj)
    (PolynomialLaurent.polynomialProjection
    (CommRingCat.of (ULift.{u} ℤ))))
  infer_instance

@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Relative.lean:87"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
instance instFlatLaurentProjection (X : QuasiCompactSchemes.{u}) :
    Flat (laurentProjection.app X).hom := by
  change Flat (pullback.fst (specULiftZIsTerminal.from X.obj)
    (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))))
  infer_instance

@[reassoc (attr := simp)] lemma plus_projection (X : QuasiCompactSchemes.{u}) :
    plus.app X ≫ polynomialProjection.app X = laurentProjection.app X := by
  apply ObjectProperty.hom_ext
  exact baseProductTransformation_projection _ _ _
    (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ))) X.obj

@[reassoc (attr := simp)] lemma minus_projection (X : QuasiCompactSchemes.{u}) :
    minus.app X ≫ polynomialProjection.app X = laurentProjection.app X := by
  apply ObjectProperty.hom_ext
  exact baseProductTransformation_projection _ _ _
    (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ))) X.obj


end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
