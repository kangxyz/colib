/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.TensorBoundarySectionModel

/-! # Original numerator and factor frames retain their full-boundary scalar -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

example {B X Y : Scheme.{u}}
    (i : B ⟶ X) (p : X ⟶ Y) (L Q : Y.Modules) (M N : X.Modules)
    (E : M ≅ (pullback p).obj L) (F : N ≅ (pullback p).obj Q)
    (eM : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    (pullback i).mapIso
        (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q).symm).symm ≪≫
        pullbackTensorFrame i M N eM eN =
      (pullback i).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q) ≪≫
        pullbackTensorFrame i ((pullback p).obj L) ((pullback p).obj Q)
          (((pullback i).mapIso E).symm ≪≫ eM) (((pullback i).mapIso F).symm ≪≫ eN) := tensorBoundaryFrame_originalModel i p L Q M N E F eM eN

#print axioms tensorBoundaryFrame_originalModel

example {B X Y : Scheme.{u}}
    (i : B ⟶ X) (p : X ⟶ Y) (L Q : Y.Modules) (M N : X.Modules)
    (E : M ≅ (pullback p).obj L) (F : N ≅ (pullback p).obj Q)
    (eM : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N, ⊤))
    (t : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj Q, ⊤))
    (ht : Hom.app
      (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q).symm).hom ⊤ a =
      pullbackGlobalSections p _ t) :
    Hom.app
      ((pullback i).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q) ≪≫
        pullbackTensorFrame i ((pullback p).obj L) ((pullback p).obj Q)
          (((pullback i).mapIso E).symm ≪≫ eM)
          (((pullback i).mapIso F).symm ≪≫ eN)).hom ⊤
      (pullbackGlobalSections i _ (pullbackGlobalSections p _ t)) =
    Hom.app (pullbackTensorFrame i M N eM eN).hom ⊤ (pullbackGlobalSections i _ a) := tensorBoundaryFrame_originalSection i p L Q M N E F eM eN a t ht

#print axioms tensorBoundaryFrame_originalSection

end AlgebraicGeometry.Scheme.Modules
