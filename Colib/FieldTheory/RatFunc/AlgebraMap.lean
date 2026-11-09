/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.CoefficientMap

/-!
# The native rational scalar algebra and coefficient map

The scoped Mathlib rational-function algebra is the existing mapRingHom on
polynomial coefficients. No rational-function field, homomorphism, or algebra
structure is introduced. This supplies the exact scalar square used below root
field comparisons and native finite-extension norms.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc nonZeroDivisors
attribute [local instance] Polynomial.algebra

namespace RatFunc

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- The native scoped rational algebra map is the literal coefficient extension
on rational functions. -/
theorem algebraMap_eq_mapRingHom :
    algebraMap (RatFunc k) (RatFunc L) =
      RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k L))
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k L)) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
    RatFunc.mapRingHom_algebraMap]
  rfl

end RatFunc
