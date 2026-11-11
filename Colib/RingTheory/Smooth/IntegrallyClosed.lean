/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.RingTheory.Smooth.Normal

/-!
# Smooth field algebras satisfy the native integral-closure hypothesis

This is a direct specialization of native normal ascent (033C) and normal
integral closure in the total fraction ring (034M). The coefficient algebra
need not itself be a field, finite-dimensional, or factorial. A domain
hypothesis is imposed separately by the affine rational-divisor equivalence.
-/

@[expose] public section

/-- Smooth algebras over a field are integrally closed in their total fraction ring. -/
theorem Algebra.Smooth.isIntegrallyClosed_of_field (k R : Type*) [Field k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] : IsIntegrallyClosed R :=
  (Algebra.isNormalRing_of_smooth k R (IsNormalRing.of_isIntegrallyClosed k)).isIntegrallyClosed
