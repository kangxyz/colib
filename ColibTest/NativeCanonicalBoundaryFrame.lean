/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CanonicalBoundaryFrame
open CategoryTheory AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
variable {X Z : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
  (i : Z ⟶ X) (h : Disjoint (Set.range i) (D.support : Set X))
example : D.comap i = ⊤ := divisor_comap_eq_top_of_disjoint D i h
example : (canonicalDisjointBoundaryFrame D i h).hom.app ⊤
    (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)) = 1 :=
  canonicalDisjointBoundaryFrame_coordinate D i h
#check relativeGraphBoundaryFrame
#check relativeGraphBoundaryFrame_coordinate
