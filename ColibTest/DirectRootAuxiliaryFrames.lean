/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.DirectRootAuxiliaryFrames

/-! # Original pair and auxiliary frame at one direct-root stage -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

example
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (c : Cone C) (hc : IsLimit c) [∀ i, CompactSpace (C.obj i)]
    [∀ i, QuasiSeparatedSpace (C.obj i)]
    (ι : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (bLim : cB.pt ⟶ c.pt) (hSquare : ∀ i, cB.π.app i ≫ ι.app i = bLim ≫ c.π.app i)
    (i : I) (L : (C.obj i).Modules)
    [SheafOfModules.IsInvertible (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property L]
    (M N : c.pt.Modules) (E : M ≅ (pullback (c.π.app i)).obj L)
    (hN : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property N)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤)) (eN : (pullback bLim).obj N ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections bLim N b) = (1 : Γ(cB.pt, ⊤))) :
    ∃ (j : I) (d : j ⟶ i) (Nj : (C.obj j).Modules)
      (_hNj : SheafOfModules.IsInvertible (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property Nj)
      (F : N ≅ (pullback (c.π.app j)).obj Nj)
      (eAux : (pullback (ι.app j)).obj Nj ≅ SheafOfModules.unit (B.obj j).ringCatSheaf)
      (a' : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj j).sheaf).obj
        ((pullback (C.map d)).obj L)).obj Nj, ⊤)) (b' : Γ(Nj, ⊤)),
      Hom.app
        (tensorProductIso c.pt.sheaf.obj c.pt.ringCatSheaf.property
          (refinedSectionModelIso (c.π.app j) (C.map d) (c.π.app i) (c.w d) L E) F ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (c.π.app j)
            ((pullback (C.map d)).obj L) Nj).symm).hom ⊤ a =
        pullbackGlobalSections (c.π.app j) _ a' ∧
      Hom.app F.hom ⊤ b = pullbackGlobalSections (c.π.app j) Nj b' ∧
      pullbackBoundaryTrivialization (cB.π.app j) (ι.app j) bLim (c.π.app j)
        (hSquare j) Nj eAux = ((pullback bLim).mapIso F).symm ≪≫ eN ∧
      Hom.app eAux.hom ⊤ (pullbackGlobalSections (ι.app j) Nj b') = (1 : Γ(B.obj j, ⊤)) :=
  exists_directRoot_auxiliaryFrames_of_isLimit B C c hc ι cB hcB bLim hSquare i L M N E hN a b eN hb

#print axioms exists_directRoot_auxiliaryFrames_of_isLimit

end AlgebraicGeometry.Scheme.Modules
