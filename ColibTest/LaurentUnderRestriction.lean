/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.LaurentUnderSquare

/-! Restriction of the fixed base is contravariant; all actual maps and composites survive. -/
noncomputable section
open CategoryTheory CommRingCat.PolynomialLaurent
universe u
variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
variable (a : Under T) {b c : Under T} (h : a ⟶ b) (k : b ⟶ c)

example : (Under.map f).obj ((Under.map g).obj a) = (Under.map (f ≫ g)).obj a := rfl
example : ((Under.map f).obj ((Under.map g).obj a)).hom = f ≫ g ≫ a.hom := rfl
example : polynomialUnderFunctor T ⋙ Under.map (f ≫ g) =
    Under.map g ⋙ Under.map f ⋙ polynomialUnderFunctor R := by
  rw [polynomialUnderFunctor_comp_map, Under.mapComp_eq, Functor.assoc]
example : laurentUnderFunctor T ⋙ Under.map (f ≫ g) =
    Under.map g ⋙ Under.map f ⋙ laurentUnderFunctor R := by
  rw [laurentUnderFunctor_comp_map, Under.mapComp_eq, Functor.assoc]
example : (Under.map (f ≫ g)).map ((polynomialUnderCoefficient T).app a) =
    (polynomialUnderCoefficient R).app ((Under.map (f ≫ g)).obj a) :=
  polynomialUnderCoefficient_map _ _
example : (Under.map (f ≫ g)).map ((laurentUnderCoefficient T).app a) =
    (laurentUnderCoefficient R).app ((Under.map (f ≫ g)).obj a) :=
  laurentUnderCoefficient_map _ _
example : (Under.map (f ≫ g)).map ((underToLaurent T).app a) =
    (underToLaurent R).app ((Under.map (f ≫ g)).obj a) := underToLaurent_map _ _
example : (Under.map (f ≫ g)).map ((underToLaurentInvert T).app a) =
    (underToLaurentInvert R).app ((Under.map (f ≫ g)).obj a) := underToLaurentInvert_map _ _
example : (Under.map f).mapArrow.mapArrow.obj
    ((Under.map g).mapArrow.mapArrow.obj (laurentUnderSquare T a)) =
      laurentUnderSquare R ((Under.map (f ≫ g)).obj a) := rfl
example : (Under.map (f ≫ g)).mapArrow.mapArrow.map (laurentUnderSquareMap T (h ≫ k)) =
    laurentUnderSquareMap R ((Under.map (f ≫ g)).map h) ≫
      laurentUnderSquareMap R ((Under.map (f ≫ g)).map k) := by
  rw [laurentUnderSquareMap_map, Functor.map_comp]
  exact (laurentUnderSquareFunctor R).map_comp _ _
example : (Under.forget R).mapArrow.mapArrow.obj
    ((Under.map (f ≫ g)).mapArrow.mapArrow.obj (laurentUnderSquare T a)) =
      laurentSquare a.right := rfl
example : (Under.forget R).mapArrow.mapArrow.map
    ((Under.map (f ≫ g)).mapArrow.mapArrow.map (laurentUnderSquareMap T h)) =
      laurentSquareMap h.right := rfl
