/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.TensorModelRefinement

/-! # Original tensor model and section through the same canonical refinement -/
noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
example {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L N : Y.Modules) :
    canIso f g p hp (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N =
      (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback g).obj L) ((pullback g).obj N) ≪≫
          tensorProductIso W.sheaf.obj W.ringCatSheaf.property
            (canIso f g p hp L) (canIso f g p hp N) := canIso_pullbackTensorIso f g p hp L N

#print axioms AlgebraicGeometry.Scheme.Modules.canIso_pullbackTensorIso
example {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L N : Y.Modules) (M A : W.Modules)
    (eM : M ≅ (pullback p).obj L) (eA : A ≅ (pullback p).obj N) :
    tensorProductIso W.sheaf.obj W.ringCatSheaf.property eM eA ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm ≪≫
        (canIso f g p hp (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N)).symm ≪≫
        (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) =
      tensorProductIso W.sheaf.obj W.ringCatSheaf.property
        (refinedSectionModelIso f g p hp L eM) (refinedSectionModelIso f g p hp N eA) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback g).obj L) ((pullback g).obj N)).symm := tensorModelIso_refinement f g p hp L N M A eM eA

#print axioms AlgebraicGeometry.Scheme.Modules.tensorModelIso_refinement
example {W X Y : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (p : W ⟶ Y) (hp : f ≫ g = p)
    (L N : Y.Modules) (M A : W.Modules)
    (eM : M ≅ (pullback p).obj L) (eA : A ≅ (pullback p).obj N)
    (s : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).obj M).obj A, ⊤))
    (t : Γ((pullback g).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N), ⊤))
    (ht : Hom.app
      (refinedSectionModelIso f g p hp
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N)
        (tensorProductIso W.sheaf.obj W.ringCatSheaf.property eM eA ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm)).hom ⊤ s =
      pullbackGlobalSections f _ t) :
    Hom.app
      (tensorProductIso W.sheaf.obj W.ringCatSheaf.property
        (refinedSectionModelIso f g p hp L eM) (refinedSectionModelIso f g p hp N eA) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback g).obj L) ((pullback g).obj N)).symm).hom ⊤ s =
      pullbackGlobalSections f _
        (Hom.app (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N).hom ⊤ t) := tensorModelIso_refinement_section f g p hp L N M A eM eA s t ht

#print axioms AlgebraicGeometry.Scheme.Modules.tensorModelIso_refinement_section
