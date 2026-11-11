/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundarySupport

/-! Whole boundary and whole polynomial-family scope examples. UNCOMPILED. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.PolynomialSectionPencil

universe u

variable {R : Type u} [CommRing R] {X Z : Scheme.{u}}
  (b : X ⟶ Spec (.of R)) (i : Z ⟶ X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (a c : Γ(L, ⊤))
  (h : pullbackGlobalSections i L a = pullbackGlobalSections i L c)
  (e : (Scheme.Modules.pullback i).obj L ⟶ SheafOfModules.unit Z.ringCatSheaf)
  (he : e.app ⊤ (pullbackGlobalSections i L a) = 1)

example : (familyZero b L a c).comap (parameterMap b i) = ⊤ :=
  familyZero_comap_boundary_eq_top b i L a c h e he

example {C : Scheme.{u}} (j : C ⟶ X)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    Set.range (familyZero b L a c).subschemeι ⊆ Set.range (parameterMap b j) :=
  familyZero_whole_support_subset b i L a c j hcover h e he

example {S C : Scheme.{u}} (bS : S ⟶ Spec (.of R)) (f : X ⟶ S)
    [IsProper f] [IsAffine S] (j : C ⟶ X) [IsOpenImmersion j] [C.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ f)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    Flat (((familyZero (f ≫ bS) L a c).comap (parameterMap (f ≫ bS) j)).subschemeι ≫
      (parameterMap (f ≫ bS) j ≫ parameterMap bS f)) :=
  (finite_relativeCartier_family_on_open_of_boundary_frame i L a c bS f j hcover h e he).2.2

#check zeroScheme_eq_top_of_unit_evaluation
#check parameterBoundary_pullback_eq
#check familyZero_comap_boundary
#check parameter_boundary_cover
#check finite_relativeCartier_family_on_open_of_boundary_frame
