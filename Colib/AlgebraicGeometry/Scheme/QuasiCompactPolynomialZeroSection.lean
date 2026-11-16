/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialLaurent

/-! # The native polynomial zero section

Adapted from `Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/ZeroSection.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.Products

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The actual zero section induced by evaluation at zero. -/
def polynomialZeroSection (R : CommRingCat.{u}) : Spec R ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))

@[reassoc (attr := simp)]
lemma polynomialZeroSection_projection (R : CommRingCat.{u}) :
    polynomialZeroSection R ≫ polynomialProjection R = 𝟙 (Spec R) := by
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 R := by
    ext r
    exact Polynomial.eval_C
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, h, Spec.map_id]

end AlgebraicGeometry.Scheme.PolynomialLaurent

namespace AlgebraicGeometry.Scheme.Bass

/-- Zero evaluation on the same native polynomial product over an arbitrary scheme. -/
def nativePolynomialZero (X : AlgebraicGeometry.Scheme.{u}) :
    X ⟶ (baseProductFunctor
      (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))).obj X :=
  pullback.lift (𝟙 X)
    (specULiftZIsTerminal.from X ≫
      PolynomialLaurent.polynomialZeroSection (CommRingCat.of (ULift.{u} ℤ)))
    (by simp)

@[reassoc (attr := simp)]
theorem nativePolynomialZero_projection (X : AlgebraicGeometry.Scheme.{u}) :
    nativePolynomialZero X ≫
      (baseProductProjection
        (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))).app X =
      𝟙 X := by
  simp [nativePolynomialZero, baseProductProjection]

@[reassoc]
theorem nativePolynomialZero_naturality {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    f ≫ nativePolynomialZero Y = nativePolynomialZero X ≫
      (baseProductFunctor
        (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))).map f := by
  have h : f ≫ specULiftZIsTerminal.from Y = specULiftZIsTerminal.from X :=
    specULiftZIsTerminal.hom_ext _ _
  have h' : f ≫ (specULiftZIsTerminal.from Y ≫
      PolynomialLaurent.polynomialZeroSection (CommRingCat.of (ULift.{u} ℤ))) =
      specULiftZIsTerminal.from X ≫
        PolynomialLaurent.polynomialZeroSection (CommRingCat.of (ULift.{u} ℤ)) := by
    rw [← Category.assoc, h]
  apply pullback.hom_ext
  · simp [nativePolynomialZero, baseProductFunctor]
  · simpa [nativePolynomialZero, baseProductFunctor] using h'

/-- The natural zero section of the original endofunctor on quasi-compact schemes. -/
def polynomialZero : 𝟭 QuasiCompactSchemes.{u} ⟶ polynomialFunctor where
  app X := ⟨nativePolynomialZero X.obj⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    exact nativePolynomialZero_naturality f.hom

@[reassoc (attr := simp)]
theorem polynomialZero_projection (X : QuasiCompactSchemes.{u}) :
    polynomialZero.app X ≫ polynomialProjection.app X = 𝟙 X := by
  apply ObjectProperty.hom_ext
  exact nativePolynomialZero_projection X.obj

/-- The original projection has the same zero section at the functor level. -/
theorem polynomialZero_comp_projection : polynomialZero ≫ polynomialProjection = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  exact polynomialZero_projection X

end AlgebraicGeometry.Scheme.Bass
