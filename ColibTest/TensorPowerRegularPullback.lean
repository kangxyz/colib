/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularPullback
import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotientBoundary

/-! The original root compatibility normalizes actual ordinary powers on the full boundary. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Stacks.SheafOfModules (schemeTensorPower)

universe u

noncomputable section

variable {X B : Scheme.{u}} (i : B ⟶ X) (L P : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
  (n : ℕ) (α : schemeTensorPower X L hL (n : ℤ) ≅ P)
  (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
  (τ : (pullback i).obj P ≅ SheafOfModules.unit (ringSheaf B))

local instance :
    Stacks.SheafOfModules.IsInvertible B.presheaf B.ringCatIsSheaf ((pullback i).obj L) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom L

local instance : SheafOfModules.IsInvertible B.presheaf (ringSheafCond B)
    ((pullback i).obj L) :=
  (inferInstance : Stacks.SheafOfModules.IsInvertible B.presheaf B.ringCatIsSheaf
    ((pullback i).obj L)).toAlgebraicGeometry

local instance : ∀ V, IsMulCommutative ((ringSheaf B).obj.obj V) :=
  fun V => inferInstanceAs (IsMulCommutative (B.presheaf.obj V))

-- B remains arbitrary: this statement does not discard its nilpotents.
example
    (hcompat : tensorPowerMap B e n ≪≫ structureSheafTensorPowerIso B n =
      (pullbackIntegerTensorPowerIso i L hL (n : ℤ)).symm ≪≫ (pullback i).mapIso α ≪≫ τ)
    (U : X.Opens) (hU : i ⁻¹ᵁ U = ⊤) (m : Γ(L, U))
    (hm : Hom.app e.hom ⊤ (pullbackSectionHom i L U ⊤ hU.ge m) = (1 : Γ(B, ⊤))) :
    Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU.ge
      (Hom.app α.hom U (natTensorPowerRegularSection X L U m n))) = (1 : Γ(B, ⊤)) :=
  frame_rootImage_natTensorPowerRegularSection_boundary i L P n α e τ hcompat U hU m hm

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackIntegerTensorPowerIso_natTensorPowerRegularSection
#print axioms AlgebraicGeometry.Scheme.Modules.frame_rootImage_natTensorPowerRegularSection_boundary
