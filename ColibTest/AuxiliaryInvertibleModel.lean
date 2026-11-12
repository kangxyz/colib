/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryInvertibleModel

/-! # Actual auxiliary model descends after the unchanged original root stage -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
example
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (L : (D.obj i).Modules) (M N : c.pt.Modules)
    (eM : M ≅ (Scheme.Modules.pullback (c.π.app i)).obj L)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible
      c.pt.sheaf.obj c.pt.ringCatSheaf.property N) :
    ∃ (j : I) (f : j ⟶ i) (Nj : (D.obj j).Modules)
      (_hNj : AlgebraicGeometry.SheafOfModules.IsInvertible
        (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Nj)
      (_eN : N ≅ (Scheme.Modules.pullback (c.π.app j)).obj Nj),
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N ≅
        (Scheme.Modules.pullback (c.π.app j)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor (D.obj j).sheaf).obj
            ((Scheme.Modules.pullback (D.map f)).obj L)).obj Nj)) := exists_auxiliaryInvertible_tensorModel_of_isLimit D c hc i L M N eM hN

#print axioms Stacks.AlgebraicGeometry.ModuleLimits.auxiliaryTensorModelIso
#print axioms Stacks.AlgebraicGeometry.ModuleLimits.exists_auxiliaryInvertible_tensorModel_of_isLimit
