/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.LaurentUnderSquare
import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionLaurentUnit

/-! The same underlying Laurent maps preserve the existing unit and its whole ambient action. -/
noncomputable section
open CategoryTheory AlgebraicGeometry CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {a b : Under R} (f : a ⟶ b)

example (n : ℤ) : ((laurentUnderFunctor R).map f).right.hom (LaurentPolynomial.T n) =
    LaurentPolynomial.T n := laurentCoefficientMap_T f.right n
example : Units.map (Spec.map ((laurentUnderFunctor R).map f).right).appTop.hom.toMonoidHom
    (laurentCoordinate a.right) = laurentCoordinate b.right :=
  laurentCoordinate_coefficient f.right
example : Units.map (Spec.map ((laurentUnderFunctor R).map f).right).appTop.hom.toMonoidHom
    ((laurentCoordinate a.right)⁻¹) = (laurentCoordinate b.right)⁻¹ := by
  change Units.map (Spec.map (laurentCoefficientMap f.right)).appTop.hom.toMonoidHom
    ((laurentCoordinate a.right)⁻¹) = (laurentCoordinate b.right)⁻¹
  rw [map_inv, laurentCoordinate_coefficient f.right]
example : Functor.isoWhiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso a.right)
    (boundedAboveFlatAffineSectionsMap ((laurentUnderFunctor R).map f).right) =
      Functor.isoWhiskerLeft
        (boundedAboveFlatAffineSectionsMap ((laurentUnderFunctor R).map f).right)
        (boundedAboveFlatAffineSectionLaurentUnitIso b.right) :=
  boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_iso f.right
example : Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso a.right).inv
    (boundedAboveFlatAffineSectionsMap ((laurentUnderFunctor R).map f).right) =
      Functor.whiskerLeft
        (boundedAboveFlatAffineSectionsMap ((laurentUnderFunctor R).map f).right)
        (boundedAboveFlatAffineSectionLaurentUnitIso b.right).inv :=
  boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_inv f.right
