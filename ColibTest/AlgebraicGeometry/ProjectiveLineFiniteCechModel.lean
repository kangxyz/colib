/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.VectorBundleCechModel
public import Mathlib.Data.ZMod.Basic

/-! # Public API check for the finite projective Čech model -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

open projectiveSpaceOver in
example (R : CommRingCat.{u}) (M : (line R).Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv (lineCechSectionsComplex R M) P) :=
  exists_lineCechFiniteProjectiveModel R M

#print axioms AlgebraicGeometry.projectiveSpaceOver.exists_lineCechFiniteProjectiveModel

open projectiveSpaceOver in
example (M : (line (.of (ZMod 4))).Modules)
    [SheafOfModules.IsFiniteLocallyFree M] :
    ∃ P : CochainComplex (ModuleCat (ZMod 4)) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite (ZMod 4) (P.X k) ∧ Module.Projective (ZMod 4) (P.X k)) ∧
      Nonempty (HomotopyEquiv (lineCechSectionsComplex (.of (ZMod 4)) M) P) :=
  exists_lineCechFiniteProjectiveModel (.of (ZMod 4)) M

open projectiveSpaceOver in
example (M : (line (.of (ZMod 1))).Modules)
    [SheafOfModules.IsFiniteLocallyFree M] :
    ∃ P : CochainComplex (ModuleCat (ZMod 1)) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite (ZMod 1) (P.X k) ∧ Module.Projective (ZMod 1) (P.X k)) ∧
      Nonempty (HomotopyEquiv (lineCechSectionsComplex (.of (ZMod 1)) M) P) :=
  exists_lineCechFiniteProjectiveModel (.of (ZMod 1)) M
