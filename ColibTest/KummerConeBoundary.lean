/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.EtaleCohomology.KummerConeBoundary

/-! # Original Kummer signed-cone boundary regression -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex CochainComplex.finiteCoefficients
noncomputable section
universe u w w'
variable (X : Scheme.{u})
variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

example (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(X, ⊤))) :
    DerivedCategory.Q.obj (finiteCoefficients
      (((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X))⟦(-1 : ℤ)⟧) n) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X n)) :=
  Stacks.Kummer.kummerSingleFiniteIso X n hn hunit

example (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(X, ⊤))) :
    DerivedCategory.Q.map (integral
      (((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X))⟦(-1 : ℤ)⟧) n) ≫
      (Stacks.Kummer.kummerSingleFiniteIso X n hn hunit).hom =
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (Stacks.Kummer.multiplicativeSheaf.{u, 0} X)) ≫
      ((Stacks.Kummer.kummerSequence_shortExact.{u, 0} X hn hunit).extClass.hom)⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).hom.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X n))) :=
  Stacks.Kummer.integral_kummerSingleFiniteIso X n hn hunit
