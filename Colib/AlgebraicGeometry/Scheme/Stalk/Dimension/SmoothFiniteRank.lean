/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-! # Finite natural local rank of an actual smooth stalk -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Stalk/Dimension/SmoothStalkFiniteRank.lean`, blob
`8125a64bbbd6195c75e3cb38f3476855f3016aa0`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme

/-- Smooth-field regularity makes the dimension of every original stalk a natural
number. No global dimension bound or induction on the ambient scheme is needed. -/
theorem exists_nat_ringKrullDim_stalk_of_smooth
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = d := by
  let : IsRegularLocalRing (X.presheaf.stalk x) :=
    by
      obtain ⟨U, hxU, hU⟩ := isRegular_of_smooth_over_field f x
      let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
        X.presheaf.algebra_section_stalk ⟨x, hxU⟩
      let : IsLocalization.AtPrime (X.presheaf.stalk x)
          (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := U.2.isLocalization_stalk ⟨x, hxU⟩
      let : IsRegularRing Γ(X, U) := hU
      exact IsRegularRing.isRegularLocalRing_of_isLocalization
        (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk x)
  exact ⟨(IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank,
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm⟩

end AlgebraicGeometry.Scheme
