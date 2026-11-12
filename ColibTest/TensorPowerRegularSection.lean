/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularSection

/-! The actual ordinary section power retains the specified native Kummer frame. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable (X : Scheme.{u}) (L : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
  (U : X.Opens) (s : Γ(L, U))
  (e : L ≅ SheafOfModules.unit (ringSheaf X))

local instance : SheafOfModules.IsInvertible X.presheaf (ringSheafCond X) L :=
  hL.toAlgebraicGeometry

local instance :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj L).IsEquivalence :=
  @Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL

local instance : ∀ V, IsMulCommutative ((ringSheaf X).obj.obj V) :=
  fun V => inferInstanceAs (IsMulCommutative (X.presheaf.obj V))

example (he : Hom.app e.hom U s = (1 : Γ(X, U))) :
    Hom.app (tensorPowerMap X e 6 ≪≫ structureSheafTensorPowerIso X 6).hom U
      (natTensorPowerRegularSection X L U s 6) = (1 : Γ(X, U)) :=
  tensorPowerFrame_natTensorPowerRegularSection_eq_one X L U s e he 6

example : natTensorPowerRegularSection X L U s 1 =
    Hom.app (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso
      X.presheaf X.ringCatIsSheaf L).inv U s :=
  natTensorPowerRegularSection_one X L U s

#print axioms AlgebraicGeometry.Scheme.Modules.natTensorPowerRegularSection_one
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPowerFrame_natTensorPowerRegularSection_eq_one
