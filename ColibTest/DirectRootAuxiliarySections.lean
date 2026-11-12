/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.DirectRootAuxiliarySections

/-! # Original pair and auxiliary frame at one direct-root stage -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

example
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    (c : Cone C) (hc : IsLimit c) [∀ i, CompactSpace (C.obj i)]
    [∀ i, QuasiSeparatedSpace (C.obj i)] (i : I) (L : (C.obj i).Modules)
    [SheafOfModules.IsInvertible (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property L]
    (M N : c.pt.Modules) (E : M ≅ (pullback (c.π.app i)).obj L)
    (hN : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property N)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤)) :
    ∃ (j : I) (e : j ⟶ i) (Nj : (C.obj j).Modules)
      (_hNj : SheafOfModules.IsInvertible (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property Nj)
      (F : N ≅ (pullback (c.π.app j)).obj Nj) (k : I) (f : k ⟶ j)
      (a' : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj k).sheaf).obj
        ((pullback (C.map (f ≫ e))).obj L)).obj ((pullback (C.map f)).obj Nj), ⊤))
      (b' : Γ((pullback (C.map f)).obj Nj, ⊤)),
      Hom.app
        (tensorProductIso c.pt.sheaf.obj c.pt.ringCatSheaf.property
          (refinedSectionModelIso (c.π.app k) (C.map (f ≫ e)) (c.π.app i) (c.w (f ≫ e)) L E)
          (refinedSectionModelIso (c.π.app k) (C.map f) (c.π.app j) (c.w f) Nj F) ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (c.π.app k)
            ((pullback (C.map (f ≫ e))).obj L) ((pullback (C.map f)).obj Nj)).symm).hom ⊤ a =
        pullbackGlobalSections (c.π.app k) _ a' ∧
      Hom.app (refinedSectionModelIso (c.π.app k) (C.map f) (c.π.app j) (c.w f) Nj F).hom ⊤ b =
        pullbackGlobalSections (c.π.app k) _ b' :=
  exists_directRoot_auxiliarySections_of_isLimit C c hc i L M N E hN a b

#print axioms exists_directRoot_auxiliarySections_of_isLimit

end AlgebraicGeometry.Scheme.Modules
