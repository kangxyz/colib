/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Modules.Invertible.PullbackTensorAuxiliaryFrameComparison

/-! # The original auxiliary contraction square without a finite-stage root frame -/
noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u

set_option maxHeartbeats 800000 in
example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (L N : D.Modules)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    (pullback f).mapIso (pullbackTensorAuxiliaryFrame g L N eN) ≪≫
        pullbackSquareIso f g h k w L =
      pullbackSquareIso f g h k w
          (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N) ≪≫
        (pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
          pullbackTensorAuxiliaryFrame h ((pullback k).obj L) ((pullback k).obj N)
            (pullbackBoundaryTrivialization f g h k w N eN) :=
  pullbackTensorAuxiliaryFrame_square f g h k w L N eN

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorAuxiliaryFrame_square
