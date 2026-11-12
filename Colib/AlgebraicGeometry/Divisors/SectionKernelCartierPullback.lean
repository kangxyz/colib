/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartesian
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-! # Cartier kernels of actual Cartesian sections under flat pullback -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Stacks.Divisors

/-- Both the genuine base restriction F and the clopen component inclusion kappa
are flat; their actual Cartesian section squares preserve Cartier kernels. -/
theorem isEffectiveCartierDivisor_ker_cartesian_of_flat
    {S' S X' X : AlgebraicGeometry.Scheme.{u}}
    (f : X' ⟶ X) [AlgebraicGeometry.Flat f] (g : S' ⟶ S)
    (σ : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion σ]
    (σ' : S' ⟶ X') (hs : IsPullback σ' g f σ)
    [hσ : IsEffectiveCartierDivisor σ.ker] :
    IsEffectiveCartierDivisor σ'.ker := by
  rw [AlgebraicGeometry.Scheme.ker_eq_comap_of_isPullback σ' g f σ hs]
  exact isPullbackDefined_of_flat f σ.ker hσ

end Stacks.Divisors
