/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProductInterchange
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactOpenPairPolynomialZeroSection

/-!
# Independent-variable interchange for the original open-support pairs

The actual scheme product swap is applied to both entries of the open immersion. Its
naturality supplies the pair square, including for non-quasi-compact opens. The original
projections and fixed-factor maps commute with this same pair isomorphism.

Intended upstream module: `Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.OpenPairInterchange`.
The fixed product legs are quasi-compact and only the ambient entry of each pair is compact.
The current consumer is `Quillen.KTheory.Bass.OpenPairProductTransport`, which retains these
actual pair maps in the supported Bass contraction.

Source: `Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairInterchange.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.Bass

variable {S S' T T' : AlgebraicGeometry.Scheme.{u}}

/-- The actual independent-variable swap on both entries of an open-support pair. -/
def pairBaseProductSwapIso (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    [QuasiCompact p] [QuasiCompact q] :
    pairBaseProductFunctor p ⋙ pairBaseProductFunctor q ≅
      pairBaseProductFunctor q ⋙ pairBaseProductFunctor p :=
  NatIso.ofComponents (fun A => quasiCompactOpenPairProperty.isoMk
    (MorphismProperty.Arrow.isoMk
      ((baseProductSwapIso p q).app A.obj.left)
      ((baseProductSwapIso p q).app A.obj.right)
      ((baseProductSwapIso p q).hom.naturality A.obj.hom).symm))
    (by
      intro A B f
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Arrow.Hom.ext
      · exact (baseProductSwapIso p q).hom.naturality f.hom.left
      · exact (baseProductSwapIso p q).hom.naturality f.hom.right)

/-- The open entry is the original scheme swap, without a compactness condition on that open. -/
@[simp]
theorem pairBaseProductSwapIso_hom_left (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    [QuasiCompact p] [QuasiCompact q] (A : QuasiCompactOpenPairs.{u}) :
    ((pairBaseProductSwapIso p q).hom.app A).hom.left =
      (baseProductSwapIso p q).hom.app A.obj.left := rfl

/-- The ambient entry retains the same original independent-variable swap. -/
@[simp]
theorem pairBaseProductSwapIso_hom_right (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    [QuasiCompact p] [QuasiCompact q] (A : QuasiCompactOpenPairs.{u}) :
    ((pairBaseProductSwapIso p q).hom.app A).hom.right =
      (baseProductSwapIso p q).hom.app A.obj.right := rfl

/-- The literal pair swap is involutive on both original entries. -/
theorem pairBaseProductSwapIso_trans (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    [QuasiCompact p] [QuasiCompact q] :
    pairBaseProductSwapIso p q ≪≫ pairBaseProductSwapIso q p = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · exact baseProductSwapMap_comp p q A.obj.left
  · exact baseProductSwapMap_comp p q A.obj.right

/-- Removing the first factor after interchange keeps the original pair projection. -/
@[reassoc]
theorem pairBaseProductSwapIso_projection_first (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact p] [QuasiCompact q]
    (A : QuasiCompactOpenPairs.{u}) :
    (pairBaseProductSwapIso p q).hom.app A ≫
        (pairBaseProductProjection p).app ((pairBaseProductFunctor q).obj A) =
      (pairBaseProductFunctor q).map ((pairBaseProductProjection p).app A) := by
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · exact baseProductSwapIso_projection_first p q A.obj.left
  · exact baseProductSwapIso_projection_first p q A.obj.right

/-- Actual maps of the first factor retain the complete open-pair square. -/
@[reassoc]
theorem pairBaseProductSwapIso_transformation_first (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (p' : S' ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    [QuasiCompact p] [QuasiCompact p'] [QuasiCompact q]
    (f : S ⟶ S') (hf : f ≫ p' = p) (A : QuasiCompactOpenPairs.{u}) :
    (pairBaseProductFunctor q).map ((pairBaseProductTransformation p p' f hf).app A) ≫
        (pairBaseProductSwapIso p' q).hom.app A =
      (pairBaseProductSwapIso p q).hom.app A ≫
        (pairBaseProductTransformation p p' f hf).app ((pairBaseProductFunctor q).obj A) := by
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · exact baseProductSwapIso_transformation_first p p' q f hf A.obj.left
  · exact baseProductSwapIso_transformation_first p p' q f hf A.obj.right

/-- Actual maps of the second factor retain the complete open-pair square. -/
@[reassoc]
theorem pairBaseProductSwapIso_transformation_second (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (q' : T' ⟶ (Spec (.of (ULift.{u} ℤ))))
    [QuasiCompact p] [QuasiCompact q] [QuasiCompact q']
    (g : T ⟶ T') (hg : g ≫ q' = q) (A : QuasiCompactOpenPairs.{u}) :
    (pairBaseProductTransformation q q' g hg).app ((pairBaseProductFunctor p).obj A) ≫
        (pairBaseProductSwapIso p q').hom.app A =
      (pairBaseProductSwapIso p q).hom.app A ≫
        (pairBaseProductFunctor p).map ((pairBaseProductTransformation q q' g hg).app A) := by
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · exact baseProductSwapIso_transformation_second p q q' g hg A.obj.left
  · exact baseProductSwapIso_transformation_second p q q' g hg A.obj.right

/-- The original positive chart commutes with the independent variable on pairs. -/
@[reassoc]
theorem pairBaseProductSwapIso_plus_second (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (A : QuasiCompactOpenPairs.{u}) :
    pairPlus.app ((pairBaseProductFunctor q).obj A) ≫
        (pairBaseProductSwapIso q (PolynomialLaurent.polynomialProjection
        (CommRingCat.of (ULift.{u} ℤ)))).hom.app A =
      (pairBaseProductSwapIso q (PolynomialLaurent.laurentProjection
        (CommRingCat.of (ULift.{u} ℤ)))).hom.app A ≫
        (pairBaseProductFunctor q).map (pairPlus.app A) :=
  pairBaseProductSwapIso_transformation_second q _ _
    (PolynomialLaurent.laurentToPolynomial (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ))) A

/-- The original inverse chart commutes with the same independent variable on pairs. -/
@[reassoc]
theorem pairBaseProductSwapIso_minus_second (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (A : QuasiCompactOpenPairs.{u}) :
    pairMinus.app ((pairBaseProductFunctor q).obj A) ≫
        (pairBaseProductSwapIso q (PolynomialLaurent.polynomialProjection
        (CommRingCat.of (ULift.{u} ℤ)))).hom.app A =
      (pairBaseProductSwapIso q (PolynomialLaurent.laurentProjection
        (CommRingCat.of (ULift.{u} ℤ)))).hom.app A ≫
        (pairBaseProductFunctor q).map (pairMinus.app A) :=
  pairBaseProductSwapIso_transformation_second q _ _
    (PolynomialLaurent.laurentMinus (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ))) A

end AlgebraicGeometry.Scheme.Bass
