/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentHomotopy

/-! Actual strict model and equality-transported unit squares, before evaluation. -/
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
universe u

example {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R) ≫
        boundedAboveFlatAffineSectionModelMap (laurentCoefficientMap f) =
      boundedAboveFlatAffineSectionModelMap f ≫
        boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion S) :=
  boundedAboveFlatAffineSectionLaurentModelSquare f

example {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionLaurentModelSquare f)) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionLaurentModelSquare f)) ≫
        Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap f)
          (boundedAboveFlatAffineSectionLaurentPullbackUnitIso S).hom :=
  boundedAboveFlatAffineSectionLaurentModelUnitSquare f

example (R : CommRingCat.{u}) (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom.app s =
      (boundedAboveFlatAffineSectionLaurentUnitIso R).hom.app
        ((boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R)).obj s) := rfl

example (R : CommRingCat.{u}) (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).inv.app s =
      (boundedAboveFlatAffineSectionLaurentUnitIso R).inv.app
        ((boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R)).obj s) := rfl
