/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryRootPullback

/-! # The original root-frame equation under an arbitrary literal boundary square -/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (M : D.Modules)
    (e : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf) :
    framePullbackIso f g h k w M (pullbackBoundaryTrivialization f g h k w M e) =
      (Scheme.Modules.pullback f).mapIso e :=
  framePullbackIso_pullbackBoundaryTrivialization f g h k w M e

example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (M L : D.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower D.toRingedSpace.presheaf (structureSheafRing D.toRingedSpace).property
      M (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (e : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : tensorPowerCongr B.toRingedSpace.presheaf
      (structureSheafRing B.toRingedSpace).property _ _ e n =
        boundaryRootPowerIso g M L n α τ) :
    tensorPowerCongr A.toRingedSpace.presheaf (structureSheafRing A.toRingedSpace).property
        _ _ (pullbackBoundaryTrivialization f g h k w M e) n =
      boundaryRootPowerIso h ((Scheme.Modules.pullback k).obj M)
        ((Scheme.Modules.pullback k).obj L) n
        ((Scheme.Modules.pullbackTensorPowerIso k M n).symm ≪≫
          (Scheme.Modules.pullback k).mapIso α)
        (pullbackBoundaryTrivialization f g h k w L τ) :=
  boundary_root_frame_pullback f g h k w M L n α τ e he

#print axioms Stacks.AlgebraicGeometry.ModuleLimits.framePullbackIso_pullbackBoundaryTrivialization
#print axioms Stacks.AlgebraicGeometry.ModuleLimits.boundary_root_frame_pullback
