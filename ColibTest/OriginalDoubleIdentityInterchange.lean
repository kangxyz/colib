/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.IdentityActionInterchangeSign

/-!
# Independent identity-action consumers

The two opposite original K-operation orders multiply to the identity. When
both identity automorphisms coincide, their composite is two-torsion. The
latter statement does not assert that the composite vanishes.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v
namespace ColibTest.DoubleIdentityInterchange
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Opposite orders of two independent original actions cancel on every original K-class. -/
theorem opposite_orders_cancel (e e' : 𝟭 (AsSmall.{0} C) ≅ 𝟭 (AsSmall.{0} C))
    (n : ℕ) (a : W.K n) :
    originalKSelfTrackOperation W W (prespectrumIsoHomotopy
          (𝟙 (asSmallCategory W)) e') (n + 1)
        (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) n a) *
      originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) (n + 1)
        (originalKSelfTrackOperation W W (prespectrumIsoHomotopy
          (𝟙 (asSmallCategory W)) e') n a) = 1 := by
  rw [originalKIdentityAction_interchange_sign W e e' n a]
  exact inv_mul_cancel _

/-- Repeating one actual identity action gives two-torsion, including input K-zero. -/
theorem same_action_two_torsion (e : 𝟭 (AsSmall.{0} C) ≅ 𝟭 (AsSmall.{0} C))
    (n : ℕ) (a : W.K n) :
    (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) (n + 1)
      (originalKSelfTrackOperation W W
        (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) n a)) ^ 2 = 1 := by
  let b := originalKSelfTrackOperation W W
    (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) (n + 1)
    (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) n a)
  have hb : b = b⁻¹ := originalKIdentityAction_interchange_sign W e e n a
  calc
    b ^ 2 = b * b := pow_two b
    _ = b⁻¹ * b := congrArg (fun c ↦ c * b) hb
    _ = 1 := inv_mul_cancel b

end ColibTest.DoubleIdentityInterchange
