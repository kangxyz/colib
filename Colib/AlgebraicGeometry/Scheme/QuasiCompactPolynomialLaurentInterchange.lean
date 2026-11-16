/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialLaurent

/-!
# Polynomial and Laurent charts under product interchange

The existing positive and inverted charts commute with either independent factor of
the actual integer-base product swap. Each equation retains the original chart map.

Source: archive Quillen/AlgebraicGeometry/Scheme/BaseProductInterchange.lean
SHA256: 7ec69cef161801f81533c1215b27e6b3aa885c09809f00068df9088897cf3f44
Selection: lines 233-279, the four actual polynomial/Laurent chart squares.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

open AlgebraicGeometry.Scheme.Products

namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

local notation "Z" => CommRingCat.of (ULift ℤ)

variable {T : AlgebraicGeometry.Scheme.{u}}

/-- The original positive chart in the first factor keeps both independent product variables. -/
@[reassoc]
theorem qcBaseProductSwapIso_plus_first (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}) :
    (qcBaseProductFunctor q).map (plus.app X) ≫
        (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection Z) q).hom.app X =
      (qcBaseProductSwapIso (PolynomialLaurent.laurentProjection Z) q).hom.app X ≫
        plus.app ((qcBaseProductFunctor q).obj X) := by
  apply ObjectProperty.hom_ext
  exact baseProductSwapIso_transformation_first _ _ q
    (PolynomialLaurent.laurentToPolynomial Z)
    (PolynomialLaurent.laurentToPolynomial_projection Z) X.obj

/-- The original inverted chart in the first factor keeps the same literal swap. -/
@[reassoc]
theorem qcBaseProductSwapIso_minus_first (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}) :
    (qcBaseProductFunctor q).map (minus.app X) ≫
        (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection Z) q).hom.app X =
      (qcBaseProductSwapIso (PolynomialLaurent.laurentProjection Z) q).hom.app X ≫
        minus.app ((qcBaseProductFunctor q).obj X) := by
  apply ObjectProperty.hom_ext
  exact baseProductSwapIso_transformation_first _ _ q
    (PolynomialLaurent.laurentMinus Z)
    (PolynomialLaurent.laurentMinus_projection Z) X.obj

/-- The original positive chart in the second factor has the opposite-side placement. -/
@[reassoc]
theorem qcBaseProductSwapIso_plus_second (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}) :
    plus.app ((qcBaseProductFunctor q).obj X) ≫
        (qcBaseProductSwapIso q (PolynomialLaurent.polynomialProjection Z)).hom.app X =
      (qcBaseProductSwapIso q (PolynomialLaurent.laurentProjection Z)).hom.app X ≫
        (qcBaseProductFunctor q).map (plus.app X) := by
  apply ObjectProperty.hom_ext
  exact baseProductSwapIso_transformation_second q _ _
    (PolynomialLaurent.laurentToPolynomial Z)
    (PolynomialLaurent.laurentToPolynomial_projection Z) X.obj

/-- The original inverted chart in the second factor retains the same direction. -/
@[reassoc]
theorem qcBaseProductSwapIso_minus_second (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}) :
    minus.app ((qcBaseProductFunctor q).obj X) ≫
        (qcBaseProductSwapIso q (PolynomialLaurent.polynomialProjection Z)).hom.app X =
      (qcBaseProductSwapIso q (PolynomialLaurent.laurentProjection Z)).hom.app X ≫
        (qcBaseProductFunctor q).map (minus.app X) := by
  apply ObjectProperty.hom_ext
  exact baseProductSwapIso_transformation_second q _ _
    (PolynomialLaurent.laurentMinus Z)
    (PolynomialLaurent.laurentMinus_projection Z) X.obj

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
