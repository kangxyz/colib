/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.Basic

/-! # Smoothness of the actual principal base localization

The native smooth-localization and composition theorems supply the instance
used locally by the monic-neighborhood construction. Generalizes the coefficient
base from a field to a commutative ring in
`Motivic/Aglib/RingTheory/Smooth/Localization.lean`, blob
`0dbbc8bdef86771669ebe6afc37b94a6986628f8` at
`kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public section

namespace Algebra.Smooth

/-- Principal base shrinking preserves the given smooth coefficient algebra. -/
theorem away_smooth {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] (r : R) : Algebra.Smooth k (Localization.Away r) := by
  let : Algebra.Smooth R (Localization.Away r) := of_isLocalization_Away r
  exact Algebra.Smooth.comp k R (Localization.Away r)

end Algebra.Smooth
