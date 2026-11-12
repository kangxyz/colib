/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Stalk.Dimension.Generization

/-! # Zero local rank on an integral scheme identifies its original generic point -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Stalk/Dimension/StalkRankZero.lean`, blob
`cc29f53aaf98032d2d1dd4dd824871e02cbfeeb3`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
open AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme

/-- On an integral scheme, zero dimension of the actual local ring means the
point is the actual generic point. -/
theorem eq_genericPoint_of_stalk_rank_zero {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 0) : x = genericPoint X := by
  rw [ringKrullDim_stalk_eq_coheight] at hx
  have h : Order.coheight x = 0 := WithBot.coe_eq_coe.mp hx
  have hm := Order.coheight_eq_zero.mp h
  have hle : x ≤ genericPoint X := genericPoint_specializes x
  exact ((show genericPoint X ⤳ x from hle).antisymm (hm hle)).eq.symm

end AlgebraicGeometry.Scheme
