/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot

/-!
# Literal pullback of an original boundary root frame

Pulling back the specified root, boundary trivialization and root frame through the same
commutative square preserves their actual power equation. No new root or frame is selected.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance instBoundaryRootPullbackInvertiblePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

local instance instBoundaryRootPullbackInvertibleUnit
    (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

local instance instBoundaryRootPullbackInvertiblePullbackUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom _
    inferInstance

private theorem normalize_frame {C : Type*} [Category C] {A B U V : C}
    (s : A ≅ B) (e : A ≅ U) (u : U ≅ V) :
    s ≪≫ (s.symm ≪≫ e ≪≫ u) ≪≫ u.symm = e := by
  simp [Iso.trans_assoc]

private theorem cancel_power_comparison {C : Type*} [Category C] {A B U V : C}
    (a : A ≅ B) (b : U ≅ V) (e : A ≅ U) (d : B ≅ V)
    (h : e ≪≫ b = a ≪≫ d) : a ≪≫ d ≪≫ b.symm = e := by
  simpa [Iso.trans_assoc] using congrArg (fun z => z ≪≫ b.symm) h.symm

/-- Normalizing the literal square pullback of a frame recovers its functorial pullback. -/
theorem framePullbackIso_pullbackBoundaryTrivialization {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (M : D.Modules)
    (e : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf) :
    framePullbackIso f g h k w M (pullbackBoundaryTrivialization f g h k w M e) =
      (Scheme.Modules.pullback f).mapIso e := by
  exact normalize_frame (pullbackSquareIso f g h k w M)
    ((Scheme.Modules.pullback f).mapIso e) (Scheme.Modules.pullbackUnitIso f)

/-- The original root frame retains its power equation under literal boundary-square pullback.
The root is pulled back with the native tensor-power comparison, and both boundary frames use
exactly the same square and unit comparisons. -/
theorem boundary_root_frame_pullback {A B C D : Scheme.{u}}
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
        (pullbackBoundaryTrivialization f g h k w L τ) := by
  apply (boundary_root_frame_pullback_iff f g h k w M L n α τ _).mpr
  rw [framePullbackIso_pullbackBoundaryTrivialization]
  have hc := cancel_power_comparison
    (Scheme.Modules.pullbackTensorPowerIso f ((Scheme.Modules.pullback g).obj M) n)
    (Scheme.Modules.pullbackTensorPowerIso f (SheafOfModules.unit B.ringCatSheaf) n)
    _ _ (Scheme.Modules.pullbackTensorPowerIso_naturality f e n)
  exact hc.trans (congrArg (Scheme.Modules.pullback f).mapIso he)

end Stacks.AlgebraicGeometry.ModuleLimits
