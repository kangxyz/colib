/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryCoordinateUnit
open CategoryTheory AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {X Z : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (i : Z ⟶ X) (h : Disjoint (Set.range i) (D.support : Set X))
    (e : (Scheme.Modules.pullback i).obj (divisorSheaf D) ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (boundaryCoordinateUnit D i h e).hom.app ⊤ 1 =
      e.hom.app ⊤ (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)) :=
  boundaryCoordinateUnit_coordinate D i h e
#check zeroScheme_boundaryCoordinate_eq_top
