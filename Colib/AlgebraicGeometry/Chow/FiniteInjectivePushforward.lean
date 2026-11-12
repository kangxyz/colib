/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField

/-!
# Injectivity of finite cycle pushforward with injective point map

A finite morphism has finite nonzero residue degree at every point. If its underlying point
map is injective, the native pushforward coefficient at the image of a point is the original
coefficient times that full residue degree. Cancellation in the integers proves injectivity.
No separability, reduction, degree-one hypothesis, or dimension grading is introduced.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual residue degree of a finite morphism is positive at every point. -/
@[stacks 01TF "finite fibers are discrete, so every residue extension is finite"]
theorem residueDegree_pos_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) : 0 < f.residueDegree x := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    (isClosed_asFiber_iff_finite_residueField f x).mp isClosed_singleton
  exact Module.finrank_pos

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- With an injective point map, the entire fiber sum is the original coefficient times
its actual residue degree, which need not be one. -/
theorem finiteCyclePushforward_apply_of_injective (hf : Function.Injective f)
    (c : AlgebraicCycle X ℤ) (x : X) :
    finiteCyclePushforward f c (f x) = c x * (f.residueDegree x : ℤ) := by
  classical
  rw [finiteCyclePushforward_apply, ← finsum_set_coe_eq_finsum_mem]
  rw [finsum_eq_single _ ⟨x, by simp⟩]
  intro z hz
  exact (hz (Subtype.ext (hf z.property))).elim

/-- Finite pushforward with injective point map is injective on the original native
integer cycles. The nonzero full residue-degree weights are cancelled, not discarded. -/
@[stacks 02R4 "corollary: finite pushforward is injective when its point map is injective"]
theorem finiteCyclePushforward_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (finiteCyclePushforward f) := by
  intro c d h
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hx := congrArg (fun e : AlgebraicCycle Y ℤ => e (f x)) h
  rw [finiteCyclePushforward_apply_of_injective f hf,
    finiteCyclePushforward_apply_of_injective f hf] at hx
  have hdegree : (f.residueDegree x : ℤ) ≠ 0 := by
    exact_mod_cast (f.residueDegree_pos_of_isFinite x).ne'
  exact mul_right_cancel₀ hdegree hx

end Stacks.Chow
