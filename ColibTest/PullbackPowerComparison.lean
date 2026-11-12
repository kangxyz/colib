/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRootComparison

/-! # Regression tests for the actual tensor-power and root-frame comparisons -/

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits

universe u v

noncomputable section

local instance (X : Scheme.{v}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance {X Y : Scheme.{v}} (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance (X : Scheme.{v}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

example {X Y : Scheme.{v}} (b : X ⟶ Y) (M : Y.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M) :
    let := hM
    Scheme.Modules.pullbackIntegerTensorPowerIso b M hM (2 : ℤ) =
      Scheme.Modules.pullbackTensorPowerIso b M 2 :=
  Scheme.Modules.pullbackIntegerTensorPowerIso_nat_eq b M hM 2

-- Both equations hold for the same frame and the same specified root and trivialization.
example {X Y : Scheme.{v}} (b : X ⟶ Y) (M L : Y.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M) (n : ℕ)
    (α : Stacks.SheafOfModules.schemeTensorPower Y M hM (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback b).obj L ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : (Scheme.Modules.pullback b).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (he : let := hM
      tensorPowerCongr X.presheaf (ringSheafCond X) _ _ e n =
        boundaryRootPowerIso b M L n α τ) :
    let := hM
    tensorPowerMap X e n ≪≫ structureSheafTensorPowerIso X n =
      (Scheme.Modules.pullbackIntegerTensorPowerIso b M hM (n : ℤ)).symm ≪≫
        (Scheme.Modules.pullback b).mapIso α ≪≫ τ :=
  (Scheme.Modules.root_frame_equation_iff b M L hM n α τ e).mpr he

-- The algebra B is arbitrary module-finite: no reducedness or domain assumption is used.
example (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
    {X : Scheme.{v}} (b : Spec (CommRingCat.of B) ⟶ X) (M L : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    {n : ℕ} (hn : IsUnit (n : R))
    (α : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback b).obj L ≅
      SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    let := hM
    ∃ e : (Scheme.Modules.pullback b).obj M ≅
        SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      tensorPowerCongr (Spec (CommRingCat.of B)).presheaf
        (ringSheafCond (Spec (CommRingCat.of B))) _ _ e n =
          boundaryRootPowerIso b M L n α τ :=
  Scheme.Modules.exists_root_compatible_frame_nat_of_module_finite R B b M L hM hn α τ
