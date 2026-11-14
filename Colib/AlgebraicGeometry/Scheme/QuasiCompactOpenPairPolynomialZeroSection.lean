/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialZeroSection
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactOpenPairPolynomialLaurent

/-!
# Actual zero sections and projection triangles for supported Bass products

Both entries of the original open-support pair use the same polynomial zero
section. Their commutative square is its scheme naturality square; the original
projection therefore splits on pairs, without requiring a quasi-compact
vanishing open. Both actual Laurent charts retain this pair projection.

Source: `Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairZeroSection.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.Products

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Bass

/-- The original first projection applied to both entries of the supported product. -/
def pairBaseProductProjection {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact p] : pairBaseProductFunctor p ⟶ 𝟭 _ where
  app A := ObjectProperty.homMk
    { left := (baseProductProjection p).app A.obj.left
      right := (baseProductProjection p).app A.obj.right
      w := ((baseProductProjection p).naturality A.obj.hom).symm
      prop_hom_left := trivial
      prop_hom_right := trivial }
  naturality {A B} f := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Arrow.Hom.ext
    · exact (baseProductProjection p).naturality f.hom.left
    · exact (baseProductProjection p).naturality f.hom.right

/-- The original polynomial projection of the same open-support pair. -/
abbrev pairPolynomialProjection : pairPolynomialFunctor.{u} ⟶ 𝟭 _ :=
  pairBaseProductProjection (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))

/-- The original Laurent projection of the same open-support pair. -/
abbrev pairLaurentProjection : pairLaurentFunctor.{u} ⟶ 𝟭 _ :=
  pairBaseProductProjection (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ)))

/-- The natural zero section on both original scheme entries of the support pair. -/
def pairPolynomialZero : 𝟭 QuasiCompactOpenPairs.{u} ⟶ pairPolynomialFunctor where
  app A := ObjectProperty.homMk
    { left := nativePolynomialZero A.obj.left
      right := nativePolynomialZero A.obj.right
      w := (nativePolynomialZero_naturality A.obj.hom).symm
      prop_hom_left := trivial
      prop_hom_right := trivial }
  naturality {A B} f := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Arrow.Hom.ext
    · exact nativePolynomialZero_naturality f.hom.left
    · exact nativePolynomialZero_naturality f.hom.right

@[reassoc (attr := simp)]
theorem pairPolynomialZero_projection (A : QuasiCompactOpenPairs.{u}) :
    pairPolynomialZero.app A ≫ pairPolynomialProjection.app A = 𝟙 A := by
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · exact nativePolynomialZero_projection A.obj.left
  · exact nativePolynomialZero_projection A.obj.right

@[reassoc (attr := simp)]
theorem pairPlus_projection (A : QuasiCompactOpenPairs.{u}) :
    pairPlus.app A ≫ pairPolynomialProjection.app A = pairLaurentProjection.app A := by
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ))) A.obj.left
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ))) A.obj.right

@[reassoc (attr := simp)]
theorem pairMinus_projection (A : QuasiCompactOpenPairs.{u}) :
    pairMinus.app A ≫ pairPolynomialProjection.app A = pairLaurentProjection.app A := by
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ))) A.obj.left
  · exact baseProductTransformation_projection _ _ _
      (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ))) A.obj.right

@[simp]
theorem pairPolynomialZero_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairPolynomialZero.app A) =
      polynomialZero.app (quasiCompactOpenPairsBase.obj A) := rfl

@[simp]
theorem pairPolynomialProjection_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairPolynomialProjection.app A) =
      polynomialProjection.app (quasiCompactOpenPairsBase.obj A) := rfl

end AlgebraicGeometry.Scheme.Bass
