/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.DisjointBoundaryGluing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {D Z C : Scheme.{u}} (i : D ⟶ C) (j : Z ⟶ C) :
    Scheme.Modules.pullback (coprod.desc i j) ⋙ Scheme.Modules.restrictFunctor
        (coprod.inl : D ⟶ D ⨿ Z) ≅ Scheme.Modules.pullback i :=
  boundaryCoprodRestrictLeft i j
#check exists_iso_of_disjoint_restrictions
#check exists_boundaryCoprod_frame
#check exists_boundaryCoprod_unitAutomorphism
