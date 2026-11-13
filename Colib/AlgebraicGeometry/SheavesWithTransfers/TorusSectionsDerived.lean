/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsFunctor
public import StacksFrontier.Homology.Injectives.DerivedCategory.RightDerivedTriangulated
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# The actual derived torus reindexing

The Grothendieck structure of transfer sheaves supplies the existing
functorial K-injective resolutions. The canonical localization right
derived functor therefore has its literal unit on the original complexes.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- Apply the actual torus sections functor degreewise and localize. -/
abbrev torusSectionsComplexToDerived :
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) :=
  (torusSectionsFunctor k).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

instance : (torusSectionsComplexToDerived k).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ)) :=
  Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (torusSectionsFunctor k)

/-- The total right derived functor of the original torus sections. -/
@[no_expose]
def torusSectionsDerivedFunctor :
    DerivedCategory (SheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) :=
  (torusSectionsComplexToDerived k).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ))

/-- The actual unit of the total derived functor on the original cochain complexes. -/
@[no_expose]
def torusSectionsDerivedUnit :
    torusSectionsComplexToDerived k ⟶ DerivedCategory.Q ⋙ torusSectionsDerivedFunctor k :=
  (torusSectionsComplexToDerived k).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ))

instance : (torusSectionsDerivedFunctor k).IsRightDerivedFunctor (torusSectionsDerivedUnit k)
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ)) := by
  dsimp only [torusSectionsDerivedFunctor, torusSectionsDerivedUnit]
  infer_instance

instance : (torusSectionsDerivedFunctor k).CommShift ℤ :=
  Stacks.Injectives.commShiftOfComplexUnit (torusSectionsFunctor k)
    (torusSectionsDerivedFunctor k) (torusSectionsDerivedUnit k)

instance : (torusSectionsDerivedFunctor k).IsTriangulated :=
  Stacks.Injectives.isTriangulated_of_complexUnit (torusSectionsFunctor k)
    (torusSectionsDerivedFunctor k) (torusSectionsDerivedUnit k)

end AlgebraicGeometry.SheafWithTransfers
