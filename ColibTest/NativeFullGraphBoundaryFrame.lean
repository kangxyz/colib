/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FullGraphBoundaryFrame
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {S C Y D : Scheme.{u}} (q : C ⟶ S) [IsSeparated q]
    (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d)) :
    (compactificationInfinityDivisorFrame q j d hd).hom.app ⊤
      (pullbackGlobalSections (infinityProductMap q j d)
        (divisorSheaf (compactificationGraph q j).ker)
        (divisorSheafGlobalSection (compactificationGraph q j).ker)) = 1 :=
  compactificationInfinityDivisorFrame_coordinate q j d hd
#check exists_fullGraphDivisorFrame
#check fullGraphCanonicalCoordinate
#check fullGraphDivisorFrame_infinity_coordinate
#check fullGraphDivisorFrame_marked_coordinate
