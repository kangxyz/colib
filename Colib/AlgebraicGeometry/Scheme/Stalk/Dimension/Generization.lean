/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension

/-! # Strict local rank decrease at proper generizations -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Stalk/Dimension/StalkRankGenerization.lean`, blob
`1d36c2c06debbb2fd76a3e78bd49d0b7e124e161`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A proper generization has strictly smaller finite local rank. -/
theorem stalk_rank_lt_of_proper_generization {X : Scheme} {x y : X}
    (h : y ⤳ x) (hne : y ≠ x) (d : ℕ)
    (hd : ringKrullDim (X.presheaf.stalk x) = d) :
    ringKrullDim (X.presheaf.stalk y) < d := by
  rw [ringKrullDim_stalk_eq_coheight] at hd ⊢
  have hlt : x < y := ⟨h, fun hxy => hne (h.antisymm hxy).eq⟩
  have hle := Order.coheight_anti hlt.le
  have hx : Order.coheight x = (d : ℕ∞) := WithBot.coe_eq_coe.mp hd
  have hy : Order.coheight y < ⊤ := lt_of_le_of_lt hle (by simp [hx])
  exact hd ▸ WithBot.coe_lt_coe.mpr (Order.coheight_strictAnti hlt hy)

end AlgebraicGeometry.Scheme
