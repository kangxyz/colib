/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StrictSheafCechModel
public import Mathlib.Data.ZMod.Basic

/-! # Public API check for the actual strictly perfect sheaf Čech model -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
attribute [local instance] HasDerivedCategory.standard

open projectiveSpaceOver in
example (R : CommRingCat.{u}) (M : (line R).Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    ∃ P : CochainComplex (Spec R).Modules ℤ,
      StrictlyPerfect.IsStrictlyPerfect (X := (Spec R).toRingedSpace) P ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i)) ∧
      Nonempty (HomotopyEquiv (lineSheafCechComplex R M) P) :=
  exists_lineStrictSheafCechModel R M

open projectiveSpaceOver in
example (M : (line (.of (ZMod 4))).Modules) [SheafOfModules.IsFiniteLocallyFree M] :
    ∃ P : CochainComplex (Spec (CommRingCat.of (ZMod 4))).Modules ℤ,
      StrictlyPerfect.IsStrictlyPerfect (X := (Spec (CommRingCat.of (ZMod 4))).toRingedSpace) P ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i)) ∧
      Nonempty (HomotopyEquiv (lineSheafCechComplex (.of (ZMod 4)) M) P) :=
  exists_lineStrictSheafCechModel (.of (ZMod 4)) M

open projectiveSpaceOver in
example (M : (line (.of (ZMod 1))).Modules) [SheafOfModules.IsFiniteLocallyFree M] :
    ∃ P : CochainComplex (Spec (CommRingCat.of (ZMod 1))).Modules ℤ,
      StrictlyPerfect.IsStrictlyPerfect (X := (Spec (CommRingCat.of (ZMod 1))).toRingedSpace) P ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i)) ∧
      Nonempty (HomotopyEquiv (lineSheafCechComplex (.of (ZMod 1)) M) P) :=
  exists_lineStrictSheafCechModel (.of (ZMod 1)) M

#print axioms AlgebraicGeometry.projectiveSpaceOver.lineSheafCechSectionsIso
#print axioms AlgebraicGeometry.projectiveSpaceOver.exists_lineStrictSheafCechModel

open projectiveSpaceOver in
example (R : CommRingCat.{u}) (M : (line R).Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    ∃ P : CochainComplex (Spec R).Modules ℤ,
      StrictlyPerfect.IsStrictlyPerfect (X := (Spec R).toRingedSpace) P ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i)) ∧
      Nonempty (lineVectorBundleDerivedImage R M ≅ DerivedCategory.Q.obj P) :=
  exists_lineDerivedImageStrictModel R M

open projectiveSpaceOver in
example (R : CommRingCat.{u}) (M : (line R).Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    RingedSpace.IsPerfect (X := (Spec R).toRingedSpace) (lineVectorBundleDerivedImage R M) :=
  isPerfect_lineVectorBundleDerivedImage R M

#print axioms AlgebraicGeometry.projectiveSpaceOver.lineDerivedImageIsoOfSheafCechModel
#print axioms AlgebraicGeometry.projectiveSpaceOver.exists_lineDerivedImageStrictModel
#print axioms AlgebraicGeometry.projectiveSpaceOver.isPerfect_lineVectorBundleDerivedImage
