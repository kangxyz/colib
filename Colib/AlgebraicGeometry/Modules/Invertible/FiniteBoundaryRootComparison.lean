/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackPowerComparison
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryPowerFrames

/-!
# The original Kummer root frame in the natural-power convention

The original global root and full-boundary trivialization give the same frame equation in
both native tensor-power conventions. In particular the frame supplied over a finite algebra
of a strictly henselian local ring satisfies the natural-power equation used in limit descent.
No reducedness, integrality, or smoothness of the boundary is required.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits

universe u v

namespace AlgebraicGeometry.Scheme.Modules

local instance finiteBoundaryRootRingedInvertible (X : Scheme.{v}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance finiteBoundaryRootPullbackInvertible {X Y : Scheme.{v}} (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance finiteBoundaryRootUnitInvertible (X : Scheme.{v}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

private theorem iso_comp_eq_iff {C : Type*} [Category C] {A B D : C}
    (m : A ≅ B) (u : B ≅ D) (r : A ≅ D) :
    m ≪≫ u = r ↔ m = r ≪≫ u.symm := by
  constructor
  · intro h
    simpa using congrArg (fun z => z ≪≫ u.symm) h
  · intro h
    simpa using congrArg (fun z => z ≪≫ u) h

/-- Equality of the two full-boundary root-frame equations, for the specified root and
specified boundary trivialization. -/
@[colib_tag "COL-1109"]
theorem root_frame_equation_iff {X Y : Scheme.{v}} (b : X ⟶ Y) (M L : Y.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M) (n : ℕ)
    (α : Stacks.SheafOfModules.schemeTensorPower Y M hM (n : ℤ) ≅ L)
    (τ : (pullback b).obj L ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : (pullback b).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    let := hM
    (tensorPowerMap X e n ≪≫ structureSheafTensorPowerIso X n =
        (pullbackIntegerTensorPowerIso b M hM (n : ℤ)).symm ≪≫ (pullback b).mapIso α ≪≫ τ) ↔
      tensorPowerCongr X.presheaf (ringSheafCond X) _ _ e n =
        boundaryRootPowerIso b M L n α τ := by
  let := hM
  dsimp only
  have hm := congrArg (fun z => z ≪≫ structureSheafTensorPowerIso X n)
    (tensorPowerMap_eq_tensorPowerCongr X e n)
  have hp := congrArg (fun z => z.symm ≪≫ (pullback b).mapIso α ≪≫ τ)
    (pullbackIntegerTensorPowerIso_nat_eq b M hM n)
  constructor
  · intro h
    exact (iso_comp_eq_iff _ _ _).mp (hm.symm.trans (h.trans hp))
  · intro h
    exact hm.trans (((iso_comp_eq_iff _ _ _).mpr h).trans hp.symm)

/-- A compatible frame on the entire finite boundary exists in the natural-power convention,
with the original root and target trivialization retained. -/
@[colib_tag "COL-1109"]
theorem exists_root_compatible_frame_nat_of_module_finite
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
    {X : Scheme.{v}} (b : Spec (CommRingCat.of B) ⟶ X) (M L : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    {n : ℕ} (hn : IsUnit (n : R))
    (α : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L)
    (τ : (pullback b).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    let := hM
    ∃ e : (pullback b).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      tensorPowerCongr (Spec (CommRingCat.of B)).presheaf
        (ringSheafCond (Spec (CommRingCat.of B))) _ _ e n =
          boundaryRootPowerIso b M L n α τ := by
  let := hM
  obtain ⟨e, he⟩ := exists_root_compatible_frame_of_module_finite R B b M L hM hn α τ
  exact ⟨e, (root_frame_equation_iff b M L hM n α τ e).mp he⟩

end AlgebraicGeometry.Scheme.Modules
