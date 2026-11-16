/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectVectorBundleTensor
public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullbackRestriction
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalTensorFirstTerm

/-! # The actual tensor functor under open restriction

The comparison is induced by the native tensor comparison of Stacks 01CD.
It applies to a fixed twisting line and also to arbitrary module sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)

local notation "TX" => Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf
local notation "TY" => Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf

/-- Ordinary open restriction of the left-tensor functor uses the pulled-back line. -/
def tensorLeftOpenRestrictionModuleIso [IsOpenImmersion f] :
    (TX).obj L ⋙ restrictFunctor f ≅
      restrictFunctor f ⋙ (TY).obj ((pullback f).obj L) :=
  Functor.isoWhiskerLeft ((TX).obj L) (restrictFunctorIsoPullback f) ≪≫
    Scheme.diagonalPullbackTensorLeftIso f L ≪≫
    Functor.isoWhiskerRight (restrictFunctorIsoPullback f).symm ((TY).obj ((pullback f).obj L))

end AlgebraicGeometry.Scheme.Modules
