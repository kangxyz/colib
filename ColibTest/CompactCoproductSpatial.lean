/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductSpatial

/-! # Actual compact spatial separation, including one-coordinate inputs -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.Product SSet
open CategoryTheory CategoryTheory.Limits Topology CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity
open scoped Topology unitInterval
universe u v
namespace ColibTest.CompactCoproductSpatial
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C] (n : ℕ)

omit [HasBinaryCoproducts C] in
/-- The actual lift retains both simultaneous spatial concatenations. -/
theorem original_product_lift
    (p₀ p₁ q₀ q₁ : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    productCubeLift W n (GenLoop.transAt 0 p₀ p₁) (GenLoop.transAt 0 q₀ q₁) =
      GenLoop.transAt 0 (productCubeLift W n p₀ q₀) (productCubeLift W n p₁ q₁) :=
  productCubeLift_transAt n W p₀ p₁ q₀ q₁

/-- The compact whole null-time and separation-time family has its exact original slices. -/
theorem original_null_time
    (P : C(unitInterval, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint))
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (t s : unitInterval) :
    coproductSeparationFamily n W P (ContinuousMap.const unitInterval q) (t, s) =
      coproductSeparationPath n W (P s) q t :=
  coproductSeparationFamily_apply n W P (ContinuousMap.const unitInterval q) t s

/-- The delays keep the quotient cube late and the identity cube early. -/
theorem original_delays
    (p q : C(unitInterval, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint))
    (t s : unitInterval) :
    coproductSeparationDelayFamily n W p q (t, s) =
      coproductCube W n (genLoopDelayLeft n (σ t, p s))
        (genLoopDelayRight n (σ t, q s)) :=
  coproductSeparationDelayFamily_apply n W p q t s

/-- Both independent deformation times preserve the entire original spatial boundary. -/
theorem original_full_boundary
    (p q : C(unitInterval, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint))
    (t s : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    coproductSeparationFamily n W p q (t, s) z = W.kBasepoint :=
  coproductSeparationFamily_boundary n W p q t s z hz

omit [HasBinaryCoproducts C] in
/-- The suffix removal is the exact old coordinate-zero loop unit path. -/
theorem original_right_unit
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (t : unitInterval) :
    genLoopRightUnitPath n p t =
      GenLoop.fromLoop 0 (loopRightUnitPath (GenLoop.toLoop 0 p) t) :=
  genLoopRightUnitPath_original n p t

/-- Degree zero retains q-first spatial order without any commutativity premise. -/
theorem original_degree_zero
    (p q : GenLoop (Fin (0 + 1)) W.Delooping W.kBasepoint) :
    coproductSeparationPath 0 W p q 1 = GenLoop.transAt 0 q p :=
  (coproductSeparationPath 0 W p q).target

end ColibTest.CompactCoproductSpatial
