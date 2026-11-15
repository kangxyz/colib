/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedConvolution
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveCoefficientMap

/-! # Shift compatibility for projective derived coefficient comparisons -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ

variable [HasDerivedCategory.{w} PST(k)]

/-- A comparison induced by the original coefficient functors commutes with shift. -/
theorem projectiveDerivedMinusFunctorIso_commShift {L R : PST(k) ⥤ PST(k)}
    [L.Additive] [R.Additive] (e : L ≅ R) :
    NatTrans.CommShift (projectiveDerivedMinusFunctorIso e).hom ℤ := by
  have h : (projectiveDerivedMinusFunctorIso e).hom = projectiveDerivedMinusFunctorMap e.hom := rfl
  exact h.symm ▸ projectiveDerivedMinusFunctorMap_commShift e.hom

end AlgebraicGeometry.PresheafWithTransfers
