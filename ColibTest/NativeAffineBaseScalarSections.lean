/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.AffineBaseScalarSections
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {Z Z' : Scheme.{u}} (β : Z' ⟶ Z)
    (E : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (unitAutomorphismPullback β E).hom.app ⊤ 1 = β.appTop (E.hom.app ⊤ 1) :=
  unitAutomorphismPullback_coordinate β E
#check exists_affineBase_scalar_sections
