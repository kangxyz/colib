/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.Invertible.UnitPowerPullback

/-! # The original unit-power normalization under scheme pullback -/

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u

noncomputable section

local instance (X : Scheme.{u}) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom _
    inferInstance

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X) X.unitModule :=
  AlgebraicGeometry.isInvertible_unit X

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback f).obj Y.unitModule) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj f.toLRSHom.toShHom
      (SheafOfModules.unit Y.ringCatSheaf))

example {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Scheme.Modules.pullbackTensorPowerIso f (SheafOfModules.unit Y.ringCatSheaf) n ≪≫
      tensorPowerCongr X.presheaf (ringSheafCond X) _ _ (Scheme.Modules.pullbackUnitIso f) n ≪≫
        structureSheafTensorPowerIso X n =
    (Scheme.Modules.pullback f).mapIso (structureSheafTensorPowerIso Y n) ≪≫
      Scheme.Modules.pullbackUnitIso f :=
  Scheme.Modules.pullbackTensorPowerIso_structureSheaf f n

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pullbackTensorPowerIso f (SheafOfModules.unit Y.ringCatSheaf) 2 ≪≫
      tensorPowerMap X (Scheme.Modules.pullbackUnitIso f) 2 ≪≫ structureSheafTensorPowerIso X 2 =
    (Scheme.Modules.pullback f).mapIso (structureSheafTensorPowerIso Y 2) ≪≫
      Scheme.Modules.pullbackUnitIso f :=
  Scheme.Modules.pullbackTensorPowerIso_tensorPowerMap_unit f 2
