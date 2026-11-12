/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot

/-! # Two original linear equations descend with the same actual root-compatible frame -/

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

noncomputable section

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

example
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Limits.Cone B) (hcB : Limits.IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Limits.Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M L : (C.obj i).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M] (n : ℕ)
    (α : tensorPower (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback (b.app i)).obj L ≅
      SheafOfModules.unit (B.obj i).ringCatSheaf)
    (eLim : (Scheme.Modules.pullback bLim).obj
      ((Scheme.Modules.pullback (cC.π.app i)).obj M) ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (heLim : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ eLim n =
        boundaryRootPowerIso bLim ((Scheme.Modules.pullback (cC.π.app i)).obj M)
          ((Scheme.Modules.pullback (cC.π.app i)).obj L) n
          ((Scheme.Modules.pullbackTensorPowerIso (cC.π.app i) M n).symm ≪≫
            (Scheme.Modules.pullback (cC.π.app i)).mapIso α)
          (pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
            (cC.π.app i) (hb i) L τ)) :
    let A := (Scheme.Modules.pullback (b.app i)).obj M
    let U := SheafOfModules.unit (B.obj i).ringCatSheaf
    let N := framePullbackIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M eLim
    ∀ (P : Fin 2 → (B.obj i).Modules)
      [∀ x, (P x).IsFinitePresentation] (s : ∀ x, P x ⟶ A) (t : ∀ x, P x ⟶ U),
      (∀ x, (Scheme.Modules.pullback (cB.π.app i)).map (s x) ≫ N.hom =
        (Scheme.Modules.pullback (cB.π.app i)).map (t x)) →
      ∃ (j : I) (f : j ⟶ i)
        (e : (Scheme.Modules.pullback (b.app j)).obj
          ((Scheme.Modules.pullback (C.map f)).obj M) ≅
            SheafOfModules.unit (B.obj j).ringCatSheaf),
        let m := framePullbackIso (B.map f) (b.app i) (b.app j) (C.map f)
          (b.naturality f) M e
        ((Scheme.Modules.pullback (cB.π.app j)).map m.hom ≫
            canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) U =
          canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) A ≫ N.hom) ∧
        (tensorPowerCongr (B.obj j).toRingedSpace.presheaf
          (structureSheafRing (B.obj j).toRingedSpace).property _ _ e n =
            boundaryRootPowerIso (b.app j) ((Scheme.Modules.pullback (C.map f)).obj M)
              ((Scheme.Modules.pullback (C.map f)).obj L) n
              ((Scheme.Modules.pullbackTensorPowerIso (C.map f) M n).symm ≪≫
                (Scheme.Modules.pullback (C.map f)).mapIso α)
              (pullbackBoundaryTrivialization (B.map f) (b.app i) (b.app j) (C.map f)
                (b.naturality f) L τ)) ∧
        ∀ x, (Scheme.Modules.pullback (B.map f)).map (s x) ≫ m.hom =
          (Scheme.Modules.pullback (B.map f)).map (t x) := by
  exact exists_boundary_root_frame_comp_eq_of_isLimit_finite B C b cB hcB cC bLim hb
    i M L n α τ eLim heLim
