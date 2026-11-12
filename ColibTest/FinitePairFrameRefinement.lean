/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FinitePairFrameRefinement

/-! # One original auxiliary frame refinement retains both original finite sections -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v
namespace FinitePairFrameRefinementRegression
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

example
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (B C D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (c : Cone C) (bLim : cB.pt ⟶ c.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ c.π.app i)
    (q : C ⟶ D)
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (i : I) (F : Bool → (C.obj i).Modules) [∀ z, (F z).IsFinitePresentation]
    [∀ z, SheafOfModules.IsInvertible (C.obj i).sheaf.obj
      (C.obj i).ringCatSheaf.property (F z)]
    (M : Bool → c.pt.Modules)
    [∀ z, SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property (M z)]
    (E : ∀ z, M z ≅ (Scheme.Modules.pullback (c.π.app i)).obj (F z))
    (sOriginal : ∀ z, Γ(M z, ⊤)) (s : ∀ z, Γ(F z, ⊤))
    (hrec : ∀ z, Hom.app (E z).hom ⊤ (sOriginal z) =
      pullbackGlobalSections (c.π.app i) (F z) (s z))
    (hfin : ∀ z, Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme (C.obj i) (F z) (s z)).subschemeι ≫ q.app i))
    (eOriginal : (Scheme.Modules.pullback bLim).obj (M false) ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hOne : Hom.app eOriginal.hom ⊤
      (pullbackGlobalSections bLim (M false) (sOriginal false)) = (1 : Γ(cB.pt, ⊤))) :
    let eLim := (Scheme.Modules.pullback bLim).mapIso (E false).symm ≪≫ eOriginal
    ∃ (j : I) (f : j ⟶ i)
      (e : (Scheme.Modules.pullback (b.app j)).obj ((Scheme.Modules.pullback (C.map f)).obj (F false)) ≅
        SheafOfModules.unit (B.obj j).ringCatSheaf),
      ((Scheme.Modules.pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) (F false)).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((Scheme.Modules.pullback (b.app i)).obj (F false)) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (c.π.app i) (hb i) (F false)).hom ≫
          eLim.hom) ∧
      Hom.app e.hom ⊤
        (pullbackGlobalSections (b.app j) ((Scheme.Modules.pullback (C.map f)).obj (F false))
          (pullbackGlobalSections (C.map f) (F false) (s false))) = (1 : Γ(B.obj j, ⊤)) ∧
      ∀ z, Hom.app
          (refinedSectionModelIso (c.π.app j) (C.map f) (c.π.app i) (c.w f) (F z) (E z)).hom ⊤
          (sOriginal z) =
        pullbackGlobalSections (c.π.app j) ((Scheme.Modules.pullback (C.map f)).obj (F z))
          (pullbackGlobalSections (C.map f) (F z) (s z)) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme (C.obj j) ((Scheme.Modules.pullback (C.map f)).obj (F z))
            (pullbackGlobalSections (C.map f) (F z) (s z))).subschemeι ≫ q.app j) ∧
        (zeroScheme (C.obj j) ((Scheme.Modules.pullback (C.map f)).obj (F z))
          (pullbackGlobalSections (C.map f) (F z) (s z))).comap (c.π.app j) =
            zeroScheme c.pt (M z) (sOriginal z) :=
  exists_original_frame_refinement_of_finitePair B C D b cB hcB c bLim hb q hcart i F M E sOriginal s hrec hfin eOriginal hOne

#print axioms AlgebraicGeometry.Scheme.Modules.exists_original_frame_refinement_of_finitePair
end FinitePairFrameRefinementRegression
