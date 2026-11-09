/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed

/-! Exact native model and prespectrum squares, before and after realization. -/
noncomputable section
open CategoryTheory Topology AlgebraicGeometry.Scheme.Modules
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
variable (R : CommRingCat.{u})

example : (boundedAboveFlatAffineSectionBassModelSquare R).left.left =
    boundedAboveFlatAffineSectionModel R := rfl
example : (boundedAboveFlatAffineSectionBassModelSquare R).left.hom.hom.toFunctor =
    boundedAboveFlatAffineSectionsMap (CommRingCat.ofHom Polynomial.C) := rfl
example : (boundedAboveFlatAffineSectionBassModelSquare R).hom.right.hom.toFunctor =
    boundedAboveFlatAffineSectionsMap (CommRingCat.ofHom Polynomial.toLaurent) := rfl
example : (boundedAboveFlatAffineSectionBassModelSquare R).right.hom.hom.toFunctor =
    boundedAboveFlatAffineSectionsMap (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) := rfl
example : (boundedAboveFlatAffineSectionBassModelSquare R).left.hom ≫
    (boundedAboveFlatAffineSectionBassModelSquare R).hom.right =
      boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R) :=
  boundedAboveFlatAffineSectionBassModelSquare_source R
example : (laurentSquare R).left.hom ≫ (laurentSquare R).hom.right =
    laurentCoefficientInclusion R := coefficient_toLaurent R
example : (laurentSquare R).hom.left ≫ (laurentSquare R).right.hom =
    laurentCoefficientInclusion R := coefficient_toLaurent_invert R
example : (boundedAboveFlatAffineSectionBassSquare R).left.hom ≫
    (boundedAboveFlatAffineSectionBassSquare R).hom.right =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) :=
  boundedAboveFlatAffineSectionBassSquare_source R

variable {R} {S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
example : (boundedAboveFlatAffineSectionBassModelSquareMap f).right.right =
    boundedAboveFlatAffineSectionModelMap (laurentCoefficientMap f) := rfl
example : (boundedAboveFlatAffineSectionBassSquareMap f).right.right =
    boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientMap f) := rfl
example : boundedAboveFlatAffineSectionBassModelSquareMap (f ≫ g) =
    boundedAboveFlatAffineSectionBassModelSquareMap f ≫
      boundedAboveFlatAffineSectionBassModelSquareMap g :=
  (laurentSquareFunctor ⋙ boundedAboveFlatAffineSectionModelFunctor.mapArrow.mapArrow).map_comp f g
