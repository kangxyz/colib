/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak

/-! # Open-detected weak equivalences on native perfect complexes

Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/OpenFibration.lean:53-95,
c561118b7795eb9780be9ed391c3251d6a4d0afd. This uses an arbitrary open immersion,
native Stacks perfectness, and ambient Mono cofibrations. No fiber or
fine-open comparison theorem is asserted. Source-only; not elaborated.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- The unchanged native perfect category with weakness detected by open restriction. -/
def perfectOpenWeakWaldhausen :=
  Waldhausen.Structure.withInverseImageWeak (perfectComplexesRestrictOpenImmersion_isExact j)

/-- Native quasi-isomorphisms are contained in the relative weak class. -/
def perfectOpenNested :=
  Waldhausen.Structure.inverseImageWeakNested (perfectComplexesRestrictOpenImmersion_isExact j)

@[simp] theorem perfectOpenWeakWaldhausen_cof :
    (perfectOpenWeakWaldhausen j).cof =
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof := rfl

@[simp] theorem perfectOpenWeakWaldhausen_zero :
    (perfectOpenWeakWaldhausen j).zero =
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).zero := rfl

/-- Cofibrations are literally ambient monomorphisms, not exact-subcategory inflations. -/
@[simp] theorem perfectOpenWeakWaldhausen_cof_iff
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) : (perfectOpenWeakWaldhausen j).cof f ↔ Mono f.hom := Iff.rfl

@[simp] theorem perfectOpenWeakWaldhausen_weq_iff
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) : (perfectOpenWeakWaldhausen j).weq f ↔
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
  Iff.rfl

instance perfectOpenWeakWaldhausen_twoOutOfThree :
    (perfectOpenWeakWaldhausen j).weq.HasTwoOutOfThreeProperty := by
  let : (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).weq.HasTwoOutOfThreeProperty :=
    Waldhausen.CofibrationClosedSubcategory.twoOutOfThree _ _ _
  exact Waldhausen.Structure.withInverseImageWeak_twoOutOfThree
    (perfectComplexesRestrictOpenImmersion_isExact j)

instance perfectOpenNested_twoOutOfThree :
    (perfectOpenNested j).coarse.weq.HasTwoOutOfThreeProperty :=
  perfectOpenWeakWaldhausen_twoOutOfThree j

/-- Ordinary restriction is exact also for the coarse source. -/
theorem perfectOpenRestrict_isExact :
    Waldhausen.IsExact (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
      (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).weq
      (perfectComplexesRestrictOpenImmersion j) :=
  Waldhausen.Structure.withInverseImageWeak_exact (perfectComplexesRestrictOpenImmersion_isExact j)
end AlgebraicGeometry.Scheme.Modules
