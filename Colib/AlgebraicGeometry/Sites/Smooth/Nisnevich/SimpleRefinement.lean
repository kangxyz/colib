/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.StandardDensityRefinement

/-!
# Composition of simple Nisnevich refinements

A simple refinement persists under enlargement of the sieve. Simple
refinements compose by substituting the refinements over the arrows of
the first sieve into its distinguished-square tree.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.HasSimpleNisnevichRefinement

variable {S : Scheme.{u}} {P : Square (SmoothSite S) → Prop}

/-- Pulling back along an arrow in the sieve gives an identity leaf. -/
theorem pullback_of_mem {X Y : SmoothSite S} {R : Sieve X} {f : Y ⟶ X}
    (hf : R f) : HasSimpleNisnevichRefinement P Y (R.pullback f) :=
  .identity (by simpa only [Sieve.pullback_apply, Category.id_comp] using hf)

/-- Enlargement of a sieve preserves its simple refinement. -/
theorem mono {X : SmoothSite S} {R T : Sieve X}
    (hR : HasSimpleNisnevichRefinement P X R) (h : R ≤ T) :
    HasSimpleNisnevichRefinement P X T := by
  induction hR with
  | identity hf => exact .identity (h _ hf)
  | empty hX => exact .empty hX
  | @square Q hQ R _ _ ih₂ ih₃ =>
    exact .square hQ (ih₂ (Sieve.pullback_monotone Q.f₂₄ h))
      (ih₃ (Sieve.pullback_monotone Q.f₃₄ h))

/-- A simple refinement over every arrow of a simply refined sieve yields
a simple refinement on the original base. -/
theorem trans {X : SmoothSite S} {R T : Sieve X}
    (hR : HasSimpleNisnevichRefinement P X R)
    (hT : ∀ ⦃Y : SmoothSite S⦄ (f : Y ⟶ X), R f →
      HasSimpleNisnevichRefinement P Y (T.pullback f)) :
    HasSimpleNisnevichRefinement P X T := by
  induction hR with
  | identity hf =>
    simpa only [Sieve.pullback_id] using hT _ hf
  | empty hX => exact .empty hX
  | @square Q hQ R _ _ ih₂ ih₃ =>
    refine .square hQ (ih₂ ?_) (ih₃ ?_)
    · intro Y f hf
      rw [← Sieve.pullback_comp]
      exact hT (f ≫ Q.f₂₄) hf
    · intro Y f hf
      rw [← Sieve.pullback_comp]
      exact hT (f ≫ Q.f₃₄) hf

end AlgebraicGeometry.Scheme.SmoothSite.HasSimpleNisnevichRefinement
