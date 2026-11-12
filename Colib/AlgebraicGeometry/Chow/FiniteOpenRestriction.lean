/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite cycle coefficients on an actual open pullback

On a restricted target the same finite fiber has the same points and the
same residue degrees. The resulting coefficient comparison applies to
the original Cartier zero cycles.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Finite cycle pushforward respects equality of the original morphism. -/
theorem finiteCyclePushforward_congr {X Y : Scheme.{u}} (f g : X ⟶ Y) [IsFinite f] [IsFinite g]
    (h : f = g) (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward f c = finiteCyclePushforward g c := by
  subst g
  rfl

/-- Passing through an open immersion preserves a finite fiber's points and
residue degrees at the original point of the open. -/
theorem finiteCyclePushforward_comp_open_apply {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (i : Y ⟶ Z) [IsOpenImmersion i] [IsFinite (f ≫ i)]
    (c : AlgebraicCycle X ℤ) (y : Y) :
    finiteCyclePushforward (f ≫ i) c (i y) = finiteCyclePushforward f c y := by
  have hfibre : (f ≫ i).base ⁻¹' {i y} = f.base ⁻¹' {y} := by
    ext x
    change i (f x) = i y ↔ f x = y
    exact i.isOpenEmbedding.injective.eq_iff
  simp only [finiteCyclePushforward_apply, hfibre, residueDegree_comp,
    residueDegree_eq_one_of_isPreimmersion i, one_mul]

/-- A finite pushforward coefficient can be computed on the actual open
pullback, using the same original residue degrees. -/
theorem finiteCyclePushforward_apply_of_open_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens)
    (c : AlgebraicCycle X ℤ) (c' : AlgebraicCycle (pullback f U.ι) ℤ)
    (h : ∀ x, c' x = c (pullback.fst f U.ι x)) (y : U.toScheme) :
    finiteCyclePushforward (pullback.snd f U.ι) c' y = finiteCyclePushforward f c (U.ι y) := by
  let a := pullback.fst f U.ι
  let b := pullback.snd f U.ι
  have hab : a ≫ f = b ≫ U.ι := pullback.condition
  have hbij : Set.BijOn a (b.base ⁻¹' {y}) (f.base ⁻¹' {U.ι y}) := by
    refine ⟨?_, a.isOpenEmbedding.injective.injOn, ?_⟩
    · intro x hx
      change f (a x) = U.ι y
      have hx' : b x = y := hx
      calc
        _ = U.ι (b x) := congrArg (fun k ↦ k x) hab
        _ = _ := congrArg U.ι hx'
    · intro x hx
      obtain ⟨z, hz, hzy⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback f U.ι) x y hx
      exact ⟨z, hzy, hz⟩
  have hdeg (x : (pullback f U.ι : Scheme.{u})) : b.residueDegree x = f.residueDegree (a x) := by
    have he := congrArg (fun k : _ ⟶ Y ↦ k.residueDegree x) hab
    rw [residueDegree_comp, residueDegree_comp, residueDegree_eq_one_of_isPreimmersion a,
      residueDegree_eq_one_of_isPreimmersion U.ι, one_mul, mul_one] at he
    exact he.symm
  rw [finiteCyclePushforward_apply, finiteCyclePushforward_apply]
  refine finsum_mem_eq_of_bijOn a hbij fun x _ ↦ ?_
  rw [h x, hdeg x]

end Stacks.Chow
