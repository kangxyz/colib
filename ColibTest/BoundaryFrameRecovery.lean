/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundaryFrameRecovery

/-! # Actual original frame recovery through the same refined module model -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v
namespace AlgebraicGeometry.Scheme.Modules

example {I : Type u} [Category.{v} I]
    (B C : I ⥤ Scheme.{u}) (b : B ⟶ C) (cB : Cone B) (cC : Cone C)
    (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    {i j : I} (f : j ⟶ i) (M : (C.obj i).Modules)
    (eLim : (pullback bLim).obj ((pullback (cC.π.app i)).obj M) ≅
      SheafOfModules.unit cB.pt.ringCatSheaf)
    (e : (pullback (b.app j)).obj ((pullback (C.map f)).obj M) ≅
      SheafOfModules.unit (B.obj j).ringCatSheaf)
    (he : (pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          eLim.hom) :
    pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim (cC.π.app j) (hb j)
        ((pullback (C.map f)).obj M) e =
      (pullback bLim).mapIso (canIso (cC.π.app j) (C.map f) (cC.π.app i) (cC.w f) M) ≪≫ eLim := boundaryFrame_recovery_pullback B C b cB cC bLim hb f M eLim e he

#print axioms boundaryFrame_recovery_pullback

example {I : Type u} [Category.{v} I]
    (B C : I ⥤ Scheme.{u}) (b : B ⟶ C) (cB : Cone B) (cC : Cone C)
    (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    {i j : I} (f : j ⟶ i) (M : (C.obj i).Modules)
    (N : cC.pt.Modules) (E : N ≅ (pullback (cC.π.app i)).obj M)
    (eOriginal : (pullback bLim).obj N ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (e : (pullback (b.app j)).obj ((pullback (C.map f)).obj M) ≅
      SheafOfModules.unit (B.obj j).ringCatSheaf)
    (he : (pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          ((pullback bLim).mapIso E.symm ≪≫ eOriginal).hom) :
    pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim (cC.π.app j) (hb j)
        ((pullback (C.map f)).obj M) e =
      (pullback bLim).mapIso
        (refinedSectionModelIso (cC.π.app j) (C.map f) (cC.π.app i) (cC.w f) M E).symm ≪≫
        eOriginal := boundaryFrame_originalModel_recovery B C b cB cC bLim hb f M N E eOriginal e he

#print axioms boundaryFrame_originalModel_recovery

end AlgebraicGeometry.Scheme.Modules
