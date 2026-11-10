/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.RatFunc.CoefficientGalois

noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

example (σ : Gal(E/k)) :
    (RatFunc.coefficientGal σ).toRingHom =
      RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom σ.toRingHom) :=
  RatFunc.coefficientGal_toRingHom σ

example [FiniteDimensional k E] [IsGalois k E]
    [IsGalois (RatFunc k) (RatFunc E)] :
    Function.Bijective
      (RatFunc.coefficientGal : Gal(E/k) → Gal((RatFunc E)/(RatFunc k))) :=
  RatFunc.coefficientGal_bijective
