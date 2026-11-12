/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatProjectionUnitNaturality

/-! Adapted from Quillen `QuillenTest/ProductUnitInterchange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

/-! # Two actual factor swaps on the original double geometric unit operation -/
@[expose] public section
noncomputable section
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.ProductUnitInterchange
open AlgebraicGeometry.RingedSpace
universe u

/-- Two original geometric swaps recover the original two-unit class in its original order. -/
example {S T : Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) (s : (Γ(T, ⊤))ˣ)
    (n : ℕ) (a : boundedAboveFlatPerfectK X.toRingedSpace n) :
    boundedAboveFlatPerfectKPullback (baseProductSwapMap q p X) (n + 2)
      (boundedAboveFlatPerfectKPullback (baseProductSwapMap p q X) (n + 2)
        (doubleProjectionUnitOperation q p X s r n a)) =
      doubleProjectionUnitOperation q p X s r n a := by
  rw [doubleProjectionUnitOperation_swap, map_inv, doubleProjectionUnitOperation_swap, inv_inv]
