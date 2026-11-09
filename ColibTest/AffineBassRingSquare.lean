/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.LaurentSquare
import Mathlib.Data.ZMod.Basic

/-! Concrete corners, chart orientation, coefficient functoriality, and degenerate rings. -/
noncomputable section
open CategoryTheory CommRingCat.PolynomialLaurent
universe u
variable (R : CommRingCat.{u})

example : (laurentSquare R).left.left = R := rfl
example : (laurentSquare R).left.right = CommRingCat.of (Polynomial R) := rfl
example : (laurentSquare R).right.left = CommRingCat.of (Polynomial R) := rfl
example : (laurentSquare R).right.right = CommRingCat.of (LaurentPolynomial R) := rfl
example : (laurentSquare R).left.hom = CommRingCat.ofHom Polynomial.C := rfl
example : (laurentSquare R).hom.left = CommRingCat.ofHom Polynomial.C := rfl
example : (laurentSquare R).hom.right.hom Polynomial.X = LaurentPolynomial.T 1 :=
  Polynomial.toLaurent_X
example : (laurentSquare R).right.hom.hom Polynomial.X = LaurentPolynomial.T (-1) := by
  change LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X) = _
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
example (r : R) : (laurentSquare R).right.hom.hom (Polynomial.C r) =
    LaurentPolynomial.C r := by
  change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C r)) = _
  rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
example (r : R) : (laurentSquare R).hom.right.hom (Polynomial.C r) =
    LaurentPolynomial.C r := Polynomial.toLaurent_C r

example : (laurentSquare (.of ℤ)).hom.right.hom Polynomial.X ≠
    (laurentSquare (.of ℤ)).right.hom.hom Polynomial.X := by
  intro h
  have hc := congrArg (fun p : LaurentPolynomial ℤ ↦ p.coeff 1) h
  change (Polynomial.toLaurent Polynomial.X).coeff 1 =
    (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X)).coeff 1 at hc
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T] at hc
  norm_num [LaurentPolynomial.T_apply] at hc

example : (laurentSquare (.of (ZMod 1))).right.right =
    CommRingCat.of (LaurentPolynomial (ZMod 1)) := rfl

variable {R} {S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
example : (laurentSquareMap f).left.left = f := rfl
example : (laurentSquareMap f).left.right =
    CommRingCat.ofHom (Polynomial.mapRingHom f.hom) := rfl
example : (laurentSquareMap f).right.left =
    CommRingCat.ofHom (Polynomial.mapRingHom f.hom) := rfl
example : (laurentSquareMap f).right.right =
    CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom) := rfl
example : laurentSquareMap (𝟙 R) = 𝟙 (laurentSquare R) := laurentSquareFunctor.map_id R
example : laurentSquareMap (f ≫ g) = laurentSquareMap f ≫ laurentSquareMap g :=
  laurentSquareFunctor.map_comp f g
example : (laurentSquareMap f).left.right.hom Polynomial.X = Polynomial.X :=
  Polynomial.map_X f.hom
example (k : ℤ) : (laurentSquareMap f).right.right.hom (LaurentPolynomial.T k) =
    LaurentPolynomial.T k := by
  change AddMonoidAlgebra.mapRingHom ℤ f.hom (AddMonoidAlgebra.single k 1) =
    AddMonoidAlgebra.single k 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

-- This coefficient map is not flat, but the actual square still exists without any premise.
example : (laurentSquareMap (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))).left.left =
    CommRingCat.ofHom (Int.castRingHom (ZMod 2)) := rfl
