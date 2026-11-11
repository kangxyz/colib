/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialBoundaryUnit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check correctionPolynomialMap_disjoint_evaluationGraph
#check zeroScheme_correctionBoundaryCoordinate
#check correctionBoundaryUnit_coordinate

example (R B : Type*) [CommRing R] [CommRing B] (z : Polynomial R →+* B)
    {A : Scheme} (a : A ⟶ Spec (.of (Polynomial R)))
    (h : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    (correctionBoundaryUnit R B z a h).hom.app ⊤ 1 = correctionBoundaryCoordinate R B z a :=
  correctionBoundaryUnit_coordinate R B z a h
