/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionFrames

/-! # Same-stage original boundary frame and modeled section normalization regression -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v w
example
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M : (C.obj i).Modules) [M.IsFinitePresentation]
    (N : cC.pt.Modules) (E : N ≅ (Scheme.Modules.pullback (cC.π.app i)).obj M)
    (eOriginal : (Scheme.Modules.pullback bLim).obj N ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    {κ : Type w} [Finite κ] (sOriginal : κ → Γ(N, ⊤)) (s : κ → Γ(M, ⊤))
    (hrecover : ∀ z, Hom.app E.hom ⊤ (sOriginal z) =
      pullbackGlobalSections (cC.π.app i) M (s z))
    (hs : ∀ z, Hom.app eOriginal.hom ⊤ (pullbackGlobalSections bLim N (sOriginal z)) =
      (1 : Γ(cB.pt, ⊤))) :
    let eLim := (Scheme.Modules.pullback bLim).mapIso E.symm ≪≫ eOriginal
    ∃ (j : I) (f : j ⟶ i)
      (e : (Scheme.Modules.pullback (b.app j)).obj ((Scheme.Modules.pullback (C.map f)).obj M) ≅
        SheafOfModules.unit (B.obj j).ringCatSheaf),
      ((Scheme.Modules.pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((Scheme.Modules.pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          eLim.hom) ∧
      ∀ z, Hom.app e.hom ⊤
        (pullbackGlobalSections (b.app j) ((Scheme.Modules.pullback (C.map f)).obj M)
          (pullbackGlobalSections (C.map f) M (s z))) = (1 : Γ(B.obj j, ⊤)) :=
  exists_original_boundaryFrame_modeledSections_one_of_isLimit B C b cB hcB cC bLim hb i M N E eOriginal sOriginal s hrecover hs

#print axioms AlgebraicGeometry.Scheme.Modules.exists_boundary_frame_originalSections_one_of_isLimit
#print axioms AlgebraicGeometry.Scheme.Modules.originalBoundaryFrame_section_model
#print axioms AlgebraicGeometry.Scheme.Modules.exists_original_boundaryFrame_modeledSections_one_of_isLimit
