/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionLaurentUnit

/-! Nontrivial-variable consumers of the actual section action and both evaluation routes. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.RegularSequence (globalSmulCenter)

noncomputable section

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt boundedAboveFlatPerfectGlobalUnitIso
  boundedAboveFlatAffineSectionsMap boundedAboveFlatAffineSectionUnitIso
universe u

variable (R : CommRingCat.{u}) (q : (Γ(Spec R, ⊤))ˣ)
  (s : BoundedAboveFlatAffineSections R) (j : Under R) (n : ℤ)

variable {R} {S : CommRingCat.{u}} (f : R ⟶ S)

variable (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
  (t : BoundedAboveFlatAffineSections (.of (LaurentPolynomial R)))

example :
    ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
      ((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedAboveFlatAffineSectionLaurentUnitIso R).hom.app t))).f n =
      (globalSmulCenter (Spec S)
        ((Scheme.ΓSpecIso S).inv.hom (h.hom (LaurentPolynomial.T 1)))).app
          (((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj t).obj.X n) :=
  boundedAboveFlatAffineSectionLaurentUnitIso_hom_terms h t n

example :
    ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
      ((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedAboveFlatAffineSectionLaurentUnitIso R).inv.app t))).f n =
      (globalSmulCenter (Spec S)
        ((Scheme.ΓSpecIso S).inv.hom (h.hom (LaurentPolynomial.T (-1))))).app
          (((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj t).obj.X n) :=
  boundedAboveFlatAffineSectionLaurentUnitIso_inv_terms h t n

example :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso R).hom
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f))
        (boundedAboveFlatAffineSectionLaurentUnitIso S).hom :=
  boundedAboveFlatAffineSectionLaurentUnitIso_coefficient f

example :
    Functor.isoWhiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso R)
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) =
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f))
        (boundedAboveFlatAffineSectionLaurentUnitIso S) :=
  boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_iso f

example :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso R).inv
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f))
        (boundedAboveFlatAffineSectionLaurentUnitIso S).inv :=
  boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_inv f
