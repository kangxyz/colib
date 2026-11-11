/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedFamilyRestriction
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialSectionPencil
universe u
example {R : Type u} [CommRing R] {X C : Scheme.{u}}
    (b : X ⟶ Spec (.of R)) (j : C ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (a c : Γ(L, ⊤)) :
    (familyZero b L a c).comap (parameterMap b j) =
      familyZero (j ≫ b) ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L a) (pullbackGlobalSections j L c) :=
  familyZero_comap_parameterMap b j L a c
#check parameterMap_parameter
#check parameterMap_comp
#check parameterSectionRestrictionIso_familySection
#check finite_flat_retainedFamily_of_boundary_frame
