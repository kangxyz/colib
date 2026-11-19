/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Module.RightScalarExtension
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Literal right tensor regression tests

These tests check scalar order for an explicit noncommutative matrix ring,
additivity of extension for independently universed modules, and extension to
the zero ring. The last test forbids an accidental nontriviality hypothesis.

Adapted from `QuillenTest/BalancedRightTensor.lean` at Quillen revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

noncomputable section

universe u v w z

open RightScalarExtension MulOpposite

namespace BalancedRightTensorTest

/-- An explicit noncommutative ring used to check multiplication order. -/
abbrev Coefficients := Matrix (Fin 2) (Fin 2) ℤ

example (m s t : Coefficients) :
    lift (RingHom.id Coefficients) (LinearMap.id : Coefficients →ₗ[Coefficientsᵐᵒᵖ] Coefficients)
      (op t • pure (RingHom.id Coefficients) m s) = m * s * t := by
  rw [pure_smul]
  change m * (s * t) = m * s * t
  rw [mul_assoc]

example {R : Type u} {S : Type v} [Ring R] [Ring S]
    {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {N : Type z} [AddCommGroup N] [Module Sᵐᵒᵖ N]
    (f : R →+* S) (a b : M →ₛₗ[f.op] N) :
    lift f (a + b) = lift f a + lift f b := by
  apply hom_ext_unit f
  intro m
  simp

example (x : Tensor (Int.castRingHom (ZMod 1)) ℤ) : x = 0 := by
  exact Subsingleton.elim x 0

end BalancedRightTensorTest
