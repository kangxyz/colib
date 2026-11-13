/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalUnitIdentityAction

/-! # Original scalar-action sign consumers on actual perfect K-zero

The test uses the native bounded-above flat perfect K-group and actual global units.
The two operation orders are inverse. Repeating one action gives two-torsion,
not a claim of vanishing and not a claim about a negative double quotient.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules.GlobalUnitIdentityOperation
open AlgebraicGeometry.Scheme.Modules.ProductUnitInterchange
universe u
namespace ColibTest.OriginalGlobalScalarSign

set_option maxRecDepth 4000 in
/-- Two original global unit orders cancel for any actual K-zero class. -/
theorem scalar_orders_cancel (X : Scheme.{u}) (r s : (Γ(X, ⊤))ˣ)
    (a : boundedAboveFlatPerfectK X.toRingedSpace 0) :
    unitKOperation X s 1 (unitKOperation X r 0 a) *
      unitKOperation X r 1 (unitKOperation X s 0 a) = 1 := by
  rw [unitKOperation_interchange_sign X r s 0 a]
  exact inv_mul_cancel _

set_option maxRecDepth 4000 in
/-- The unchanged original self-composite on K-zero is two-torsion. -/
theorem scalar_square_two_torsion (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (a : boundedAboveFlatPerfectK X.toRingedSpace 0) :
    (unitKOperation X r 1 (unitKOperation X r 0 a)) ^ 2 = 1 := by
  let b := unitKOperation X r 1 (unitKOperation X r 0 a)
  have hb : b = b⁻¹ := unitKOperation_interchange_sign X r r 0 a
  calc
    b ^ 2 = b * b := pow_two b
    _ = b⁻¹ * b := congrArg (fun c ↦ c * b) hb
    _ = 1 := inv_mul_cancel b

end ColibTest.OriginalGlobalScalarSign
