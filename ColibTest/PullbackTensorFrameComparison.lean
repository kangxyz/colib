/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Modules.Invertible.PullbackTensorFrameComparison

/-! # Original tensor frames under the actual square and module comparisons -/
noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u

set_option maxHeartbeats 800000 in
example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (L N : D.Modules) :
    (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) ≪≫
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        ((pullback g).obj L) ((pullback g).obj N) ≪≫
      tensorProductIso A.sheaf.obj A.ringCatSheaf.property
        (pullbackSquareIso f g h k w L) (pullbackSquareIso f g h k w N) =
    pullbackSquareIso f g h k w
        (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N) ≪≫
      (pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso h
          ((pullback k).obj L) ((pullback k).obj N) :=
  pullbackSquareIso_tensorProduct f g h k w L N

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSquareIso_tensorProduct

set_option maxHeartbeats 800000 in
example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) ≪≫
      tensorProductIso X.presheaf X.ringCatIsSheaf (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
        tensorProductLeftUnitor X.presheaf X.ringCatIsSheaf (SheafOfModules.unit X.ringCatSheaf) =
    (pullback f).mapIso (tensorProductLeftUnitor Y.presheaf Y.ringCatIsSheaf
      (SheafOfModules.unit Y.ringCatSheaf)) ≪≫ pullbackUnitIso f :=
  pullbackUnitIso_tensorProductLeftUnitor f

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_tensorProductLeftUnitor

set_option maxHeartbeats 800000 in
example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (L N : D.Modules)
    (eL : (pullback g).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    pullbackBoundaryTrivialization f g h k w
        (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N)
        (pullbackTensorFrame g L N eL eN) =
      (pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
        pullbackTensorFrame h ((pullback k).obj L) ((pullback k).obj N)
          (pullbackBoundaryTrivialization f g h k w L eL)
          (pullbackBoundaryTrivialization f g h k w N eN) :=
  pullbackBoundaryTrivialization_pullbackTensorFrame f g h k w L N eL eN

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackBoundaryTrivialization_pullbackTensorFrame

set_option maxHeartbeats 800000 in
example {X B : Scheme.{u}} (i : B ⟶ X)
    {M N M' N' : X.Modules} (E : M ≅ M') (F : N ≅ N')
    (eM : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    ((pullback i).mapIso (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F)).symm ≪≫
        pullbackTensorFrame i M N eM eN =
      pullbackTensorFrame i M' N' (((pullback i).mapIso E).symm ≪≫ eM)
        (((pullback i).mapIso F).symm ≪≫ eN) :=
  pullbackTensorFrame_naturality i E F eM eN

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorFrame_naturality
