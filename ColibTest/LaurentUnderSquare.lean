/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.LaurentUnderSquare
import Mathlib.Data.ZMod.Basic

/-! The actual four objects, structure maps, chart directions and coefficient arrows. -/
noncomputable section
open CategoryTheory CommRingCat.PolynomialLaurent
universe u
variable (R : CommRingCat.{u}) (a : Under R)

example : (laurentUnderSquare R a).left.left = a := rfl
example : (laurentUnderSquare R a).left.right =
    Under.mk (a.hom ≫ CommRingCat.ofHom Polynomial.C) := rfl
example : (laurentUnderSquare R a).right.left =
    Under.mk (a.hom ≫ CommRingCat.ofHom Polynomial.C) := rfl
example : (laurentUnderSquare R a).right.right =
    Under.mk (a.hom ≫ CommRingCat.ofHom LaurentPolynomial.C) := rfl
example : (laurentUnderSquare R a).left.left.hom = a.hom := rfl
example : (laurentUnderSquare R a).left.right.hom =
    a.hom ≫ CommRingCat.ofHom Polynomial.C := rfl
example : (laurentUnderSquare R a).right.left.hom =
    a.hom ≫ CommRingCat.ofHom Polynomial.C := rfl
example : (laurentUnderSquare R a).right.right.hom =
    a.hom ≫ CommRingCat.ofHom LaurentPolynomial.C := rfl

example : (laurentUnderSquare R a).left.hom = (polynomialUnderCoefficient R).app a := rfl
example : (laurentUnderSquare R a).hom.left = (polynomialUnderCoefficient R).app a := rfl
example : (laurentUnderSquare R a).hom.right = (underToLaurent R).app a := rfl
example : (laurentUnderSquare R a).right.hom = (underToLaurentInvert R).app a := rfl
example : (laurentUnderSquare R a).left.hom ≫ (laurentUnderSquare R a).hom.right =
    (laurentUnderSquare R a).hom.left ≫ (laurentUnderSquare R a).right.hom := by
  exact (polynomialUnderCoefficient_toLaurent R a).trans
    (polynomialUnderCoefficient_toLaurentInvert R a).symm
example : (laurentUnderSquare R a).left.hom ≫ (laurentUnderSquare R a).hom.right =
    (laurentUnderCoefficient R).app a := polynomialUnderCoefficient_toLaurent R a
example : (laurentUnderSquare R a).hom.left ≫ (laurentUnderSquare R a).right.hom =
    (laurentUnderCoefficient R).app a := polynomialUnderCoefficient_toLaurentInvert R a
example : (laurentUnderSquare R a).hom.right.right.hom Polynomial.X =
    LaurentPolynomial.T 1 := Polynomial.toLaurent_X
example : (laurentUnderSquare R a).right.hom.right.hom Polynomial.X =
    LaurentPolynomial.T (-1) := by
  change LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X) = _
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
example (r : R) : (laurentUnderSquare R a).hom.right.right.hom
    ((laurentUnderSquare R a).left.right.hom.hom r) = LaurentPolynomial.C (a.hom.hom r) :=
  Polynomial.toLaurent_C _

variable {a} {b c : Under R} (f : a ⟶ b) (g : b ⟶ c)
example : (laurentUnderSquareMap R f).left.left = f := rfl
example : (laurentUnderSquareMap R f).left.right = (polynomialUnderFunctor R).map f := rfl
example : (laurentUnderSquareMap R f).right.left = (polynomialUnderFunctor R).map f := rfl
example : (laurentUnderSquareMap R f).right.right = (laurentUnderFunctor R).map f := rfl
example : (laurentUnderSquareMap R f).right.right.right.hom =
    AddMonoidAlgebra.mapRingHom ℤ f.right.hom := rfl
example : laurentUnderSquareMap R (𝟙 a) = 𝟙 (laurentUnderSquare R a) :=
  (laurentUnderSquareFunctor R).map_id a
example : laurentUnderSquareMap R (f ≫ g) =
    laurentUnderSquareMap R f ≫ laurentUnderSquareMap R g :=
  (laurentUnderSquareFunctor R).map_comp f g
example : (Under.forget R).mapArrow.mapArrow.map (laurentUnderSquareMap R (f ≫ g)) =
    laurentSquareMap f.right ≫ laurentSquareMap g.right :=
  laurentSquareFunctor.map_comp f.right g.right

-- No nontriviality is required: the zero ring is an allowed coefficient algebra.
example : (laurentUnderSquare (CommRingCat.of ℤ)
    (Under.mk (CommRingCat.ofHom (Int.castRingHom (ZMod 1))))).right.right.right =
      CommRingCat.of (LaurentPolynomial (ZMod 1)) := rfl
example : (laurentUnderSquare (CommRingCat.of (ZMod 1)) (Under.mk (𝟙 (CommRingCat.of (ZMod 1))))).right.hom =
    (underToLaurentInvert (CommRingCat.of (ZMod 1))).app (Under.mk (𝟙 (CommRingCat.of (ZMod 1)))) := rfl
-- The coefficient arrow need not be flat: ℤ → ℤ/2 is allowed.
example : (laurentUnderSquareMap (CommRingCat.of ℤ)
    (Under.homMk (U := Under.mk (𝟙 (CommRingCat.of ℤ)))
      (V := Under.mk (CommRingCat.ofHom (Int.castRingHom (ZMod 2))))
      (CommRingCat.ofHom (Int.castRingHom (ZMod 2))) (Category.id_comp _))).left.left.right =
        CommRingCat.ofHom (Int.castRingHom (ZMod 2)) := rfl
