/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentHomotopy

/-! Nontrivial-variable consumers of the actual section action and both evaluation routes. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.RegularSequence (globalSmulCenter)

noncomputable section

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt boundedAboveFlatPerfectGlobalUnitIso
  boundedAboveFlatAffineSectionsMap boundedAboveFlatAffineSectionUnitIso
universe u

variable (R : CommRingCat.{u}) 
  (s : BoundedAboveFlatAffineSections R) (n : ℤ)

variable {R} {S : CommRingCat.{u}}

variable (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)

example :
    ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
      ((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedAboveFlatAffineSectionLaurentUnitIso R).hom.app
          ((boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R)).obj s)))).f n =
      (globalSmulCenter (Spec S)
        ((Scheme.ΓSpecIso S).inv.hom (h.hom (LaurentPolynomial.T 1)))).app
          (((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj
              ((boundedAboveFlatAffineSectionsMap
                (laurentCoefficientInclusion R)).obj s)).obj.X n) :=
  boundedAboveFlatAffineSectionLaurentUnitIso_hom_terms h
    ((boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R)).obj s) n

example :
    ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
      ((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedAboveFlatAffineSectionLaurentUnitIso R).inv.app
          ((boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R)).obj s)))).f n =
      (globalSmulCenter (Spec S)
        ((Scheme.ΓSpecIso S).inv.hom (h.hom (LaurentPolynomial.T (-1))))).app
          (((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj
              ((boundedAboveFlatAffineSectionsMap
                (laurentCoefficientInclusion R)).obj s)).obj.X n) :=
  boundedAboveFlatAffineSectionLaurentUnitIso_inv_terms h
    ((boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R)).obj s) n
