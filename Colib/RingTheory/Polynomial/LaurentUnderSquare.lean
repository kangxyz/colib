/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The original Laurent square over one fixed coefficient ring

Polynomial and Laurent extension preserve the actual structure map from a fixed ring R. The
positive and inverse-coordinate legs therefore form the original strict square in Under R,
not merely after forgetting to rings. This is the coefficient diagram used with fixed original
open-pair pullbacks; no algebra is replaced and no comparison square is assumed.

Implementation provenance: `Aglib/Algebra/Polynomial/Laurent/UnderSquare.lean` at
`2c34f185fa859e862661f939cd216b07bcccfb26`.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CommRingCat.PolynomialLaurent
variable (R : CommRingCat.{u})

/-- Original polynomial extension as an endofunctor of the fixed ring's algebra category. -/
def polynomialUnderFunctor : Under R ⥤ Under R where
  obj a := Under.mk (a.hom ≫ CommRingCat.ofHom (Polynomial.C : a.right →+* Polynomial a.right))
  map {a b} f := Under.homMk (CommRingCat.ofHom (Polynomial.mapRingHom f.right.hom)) (by
    change (a.hom ≫ CommRingCat.ofHom Polynomial.C) ≫
      CommRingCat.ofHom (Polynomial.mapRingHom f.right.hom) =
        b.hom ≫ CommRingCat.ofHom Polynomial.C
    rw [Category.assoc, ← polynomial_coefficient_square, ← Category.assoc, Under.w])
  map_id a := by apply Under.UnderMorphism.ext; exact CommRingCat.hom_ext Polynomial.mapRingHom_id
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact CommRingCat.hom_ext (Polynomial.mapRingHom_comp g.right.hom f.right.hom).symm

/-- Original Laurent extension retains the same fixed coefficient ring. -/
def laurentUnderFunctor : Under R ⥤ Under R where
  obj a := Under.mk (a.hom ≫
    CommRingCat.ofHom (LaurentPolynomial.C : a.right →+* LaurentPolynomial a.right))
  map {a b} f := Under.homMk (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.right.hom)) (by
    change (a.hom ≫ CommRingCat.ofHom LaurentPolynomial.C) ≫
      CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.right.hom) =
        b.hom ≫ CommRingCat.ofHom LaurentPolynomial.C
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change AddMonoidAlgebra.mapRingHom ℤ f.right.hom (LaurentPolynomial.C (a.hom.hom r)) =
      LaurentPolynomial.C (b.hom.hom r)
    change AddMonoidAlgebra.mapRingHom ℤ f.right.hom
      (AddMonoidAlgebra.single 0 (a.hom.hom r)) = AddMonoidAlgebra.single 0 (b.hom.hom r)
    rw [AddMonoidAlgebra.mapRingHom_single]
    exact congrArg (AddMonoidAlgebra.single 0) (ConcreteCategory.congr_hom (Under.w f) r))
  map_id a := by
    apply Under.UnderMorphism.ext
    exact CommRingCat.hom_ext AddMonoidAlgebra.mapRingHom_id
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact CommRingCat.hom_ext (AddMonoidAlgebra.mapRingHom_comp g.right.hom f.right.hom)

/-- The original polynomial coefficient inclusion is a natural algebra arrow. -/
def polynomialUnderCoefficient : 𝟭 (Under R) ⟶ polynomialUnderFunctor R where
  app a := Under.homMk (CommRingCat.ofHom (Polynomial.C : a.right →+* Polynomial a.right)) rfl
  naturality _ _ f := by apply Under.UnderMorphism.ext; exact polynomial_coefficient_square f.right

/-- The original Laurent coefficient inclusion is likewise a natural algebra arrow. -/
def laurentUnderCoefficient : 𝟭 (Under R) ⟶ laurentUnderFunctor R where
  app a := Under.homMk (CommRingCat.ofHom
    (LaurentPolynomial.C : a.right →+* LaurentPolynomial a.right)) rfl
  naturality _ _ f := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (AddMonoidAlgebra.mapRingHom_single f.right.hom 0 r).symm

/-- The positive-coordinate Laurent leg retains the original fixed-base structure equation. -/
def underToLaurent : polynomialUnderFunctor R ⟶ laurentUnderFunctor R where
  app a := Under.homMk (CommRingCat.ofHom (Polynomial.toLaurent (R := a.right))) (by
    change (a.hom ≫ CommRingCat.ofHom Polynomial.C) ≫
      CommRingCat.ofHom Polynomial.toLaurent = a.hom ≫ CommRingCat.ofHom LaurentPolynomial.C
    rw [Category.assoc, coefficient_toLaurent])
  naturality _ _ f := by apply Under.UnderMorphism.ext; exact toLaurent_naturality f.right

/-- The inverse-coordinate Laurent leg retains its original structure equation. -/
def underToLaurentInvert : polynomialUnderFunctor R ⟶ laurentUnderFunctor R where
  app a := Under.homMk (CommRingCat.ofHom
    ((LaurentPolynomial.invert (R := a.right)).toRingHom.comp Polynomial.toLaurent)) (by
      change (a.hom ≫ CommRingCat.ofHom Polynomial.C) ≫
        CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) =
          a.hom ≫ CommRingCat.ofHom LaurentPolynomial.C
      rw [Category.assoc, coefficient_toLaurent_invert])
  naturality _ _ f := by apply Under.UnderMorphism.ext; exact inverseChart_naturality f.right

/-- The original positive leg has the actual original Laurent coefficient composite. -/
theorem polynomialUnderCoefficient_toLaurent (a : Under R) :
    (polynomialUnderCoefficient R).app a ≫ (underToLaurent R).app a =
      (laurentUnderCoefficient R).app a := by
  apply Under.UnderMorphism.ext
  exact coefficient_toLaurent a.right

/-- The inverse-coordinate leg has the very same original Laurent coefficient composite. -/
theorem polynomialUnderCoefficient_toLaurentInvert (a : Under R) :
    (polynomialUnderCoefficient R).app a ≫ (underToLaurentInvert R).app a =
      (laurentUnderCoefficient R).app a := by
  apply Under.UnderMorphism.ext
  exact coefficient_toLaurent_invert a.right

/-- The original polynomial/Laurent square as an actual square over the fixed base ring. -/
def laurentUnderSquare (a : Under R) : Arrow (Arrow (Under R)) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk ((polynomialUnderCoefficient R).app a))
    (g := Arrow.mk ((underToLaurentInvert R).app a))
    ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) (by
      exact (polynomialUnderCoefficient_toLaurentInvert R a).trans
        (polynomialUnderCoefficient_toLaurent R a).symm))

/-- All four original coefficient maps preserve this fixed-base square. -/
def laurentUnderSquareMap {a b : Under R} (f : a ⟶ b) :
    laurentUnderSquare R a ⟶ laurentUnderSquare R b :=
  Arrow.homMk
    (Arrow.homMk f ((polynomialUnderFunctor R).map f)
      ((polynomialUnderCoefficient R).naturality f))
    (Arrow.homMk ((polynomialUnderFunctor R).map f) ((laurentUnderFunctor R).map f)
      ((underToLaurentInvert R).naturality f)) (by
        apply Arrow.hom_ext
        · exact (polynomialUnderCoefficient R).naturality f
        · exact (underToLaurent R).naturality f)

/-- The unchanged square is strictly functorial on original coefficient algebras. -/
def laurentUnderSquareFunctor : Under R ⥤ Arrow (Arrow (Under R)) where
  obj := laurentUnderSquare R
  map := laurentUnderSquareMap R
  map_id a := by
    apply Arrow.hom_ext
    · apply Arrow.hom_ext
      · rfl
      · exact (polynomialUnderFunctor R).map_id a
    · apply Arrow.hom_ext
      · exact (polynomialUnderFunctor R).map_id a
      · exact (laurentUnderFunctor R).map_id a
  map_comp f g := by
    apply Arrow.hom_ext
    · apply Arrow.hom_ext
      · rfl
      · exact (polynomialUnderFunctor R).map_comp f g
    · apply Arrow.hom_ext
      · exact (polynomialUnderFunctor R).map_comp f g
      · exact (laurentUnderFunctor R).map_comp f g

/-- Forgetting the algebra structure retains the original Laurent ring square literally. -/
theorem laurentUnderSquare_forget (a : Under R) :
    (Under.forget R).mapArrow.mapArrow.obj (laurentUnderSquare R a) =
      laurentSquare a.right := rfl

/-- Forgetting a coefficient-square morphism retains all four underlying ring maps. -/
theorem laurentUnderSquareMap_forget {a b : Under R} (f : a ⟶ b) :
    (Under.forget R).mapArrow.mapArrow.map (laurentUnderSquareMap R f) =
      laurentSquareMap f.right := rfl

/-- The whole fixed-base square functor forgets to the ordinary Laurent square functor. -/
theorem laurentUnderSquareFunctor_comp_forget :
    laurentUnderSquareFunctor R ⋙ (Under.forget R).mapArrow.mapArrow =
      Under.forget R ⋙ laurentSquareFunctor := rfl


variable {R} {S : CommRingCat.{u}}

/-- Restricting the fixed base along `R → S` commutes with polynomial extension. -/
theorem polynomialUnderFunctor_comp_map (f : R ⟶ S) :
    polynomialUnderFunctor S ⋙ Under.map f = Under.map f ⋙ polynomialUnderFunctor R := rfl

/-- Restricting the fixed base along `R → S` commutes with Laurent extension. -/
theorem laurentUnderFunctor_comp_map (f : R ⟶ S) :
    laurentUnderFunctor S ⋙ Under.map f = Under.map f ⋙ laurentUnderFunctor R := rfl

/-- Fixed-base restriction preserves the polynomial coefficient inclusion. -/
theorem polynomialUnderCoefficient_map (f : R ⟶ S) (a : Under S) :
    (Under.map f).map ((polynomialUnderCoefficient S).app a) =
      (polynomialUnderCoefficient R).app ((Under.map f).obj a) := rfl

/-- Fixed-base restriction preserves the Laurent coefficient inclusion. -/
theorem laurentUnderCoefficient_map (f : R ⟶ S) (a : Under S) :
    (Under.map f).map ((laurentUnderCoefficient S).app a) =
      (laurentUnderCoefficient R).app ((Under.map f).obj a) := rfl

/-- Fixed-base restriction preserves the positive Laurent chart. -/
theorem underToLaurent_map (f : R ⟶ S) (a : Under S) :
    (Under.map f).map ((underToLaurent S).app a) =
      (underToLaurent R).app ((Under.map f).obj a) := rfl

/-- Fixed-base restriction preserves the inverse-coordinate Laurent chart. -/
theorem underToLaurentInvert_map (f : R ⟶ S) (a : Under S) :
    (Under.map f).map ((underToLaurentInvert S).app a) =
      (underToLaurentInvert R).app ((Under.map f).obj a) := rfl

/-- Fixed-base restriction retains the whole square, including its four structure maps. -/
theorem laurentUnderSquare_map (f : R ⟶ S) (a : Under S) :
    (Under.map f).mapArrow.mapArrow.obj (laurentUnderSquare S a) =
      laurentUnderSquare R ((Under.map f).obj a) := rfl

/-- The four coefficient maps of the square are unchanged by fixed-base restriction. -/
theorem laurentUnderSquareMap_map (f : R ⟶ S) {a b : Under S} (g : a ⟶ b) :
    (Under.map f).mapArrow.mapArrow.map (laurentUnderSquareMap S g) =
      laurentUnderSquareMap R ((Under.map f).map g) := rfl

/-- The strict square functor commutes with contravariant restriction of the fixed base. -/
theorem laurentUnderSquareFunctor_comp_map (f : R ⟶ S) :
    laurentUnderSquareFunctor S ⋙ (Under.map f).mapArrow.mapArrow =
      Under.map f ⋙ laurentUnderSquareFunctor R := rfl

end CommRingCat.PolynomialLaurent

attribute [colib_tag "COL-0379", colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/UnderSquare.lean:26-137" "adaptation"
  "Fixed-base polynomial and Laurent functors, coefficient arrows, two oriented charts, \
  strict square, and literal forget compatibility"]
  CommRingCat.PolynomialLaurent.polynomialUnderFunctor
  CommRingCat.PolynomialLaurent.laurentUnderFunctor
  CommRingCat.PolynomialLaurent.polynomialUnderCoefficient
  CommRingCat.PolynomialLaurent.laurentUnderCoefficient
  CommRingCat.PolynomialLaurent.underToLaurent
  CommRingCat.PolynomialLaurent.underToLaurentInvert
  CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_toLaurent
  CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_toLaurentInvert
  CommRingCat.PolynomialLaurent.laurentUnderSquare
  CommRingCat.PolynomialLaurent.laurentUnderSquareMap
  CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor
  CommRingCat.PolynomialLaurent.laurentUnderSquare_forget
  CommRingCat.PolynomialLaurent.laurentUnderSquareMap_forget
  CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor_comp_forget


attribute [colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/UnderSquare.lean:26-137" "comparison"
  "Contravariant restriction of the fixed base preserves the same polynomial and Laurent \
  objects, coefficient arrows, oriented charts, and strict square"]
  CommRingCat.PolynomialLaurent.polynomialUnderFunctor_comp_map
  CommRingCat.PolynomialLaurent.laurentUnderFunctor_comp_map
  CommRingCat.PolynomialLaurent.polynomialUnderCoefficient_map
  CommRingCat.PolynomialLaurent.laurentUnderCoefficient_map
  CommRingCat.PolynomialLaurent.underToLaurent_map
  CommRingCat.PolynomialLaurent.underToLaurentInvert_map
  CommRingCat.PolynomialLaurent.laurentUnderSquare_map
  CommRingCat.PolynomialLaurent.laurentUnderSquareMap_map
  CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor_comp_map
