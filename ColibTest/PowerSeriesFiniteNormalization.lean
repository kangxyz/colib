/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.PowerSeries.FiniteNormalization
import Mathlib.FieldTheory.PurelyInseparable.Basic

noncomputable section

universe u v

example (k : Type u) [Field k] : IsJapaneseRing (PowerSeries k) :=
  PowerSeries.isJapaneseRing_of_field k

-- The auxiliary field may live in a distinct universe and need not be separable.
example (k : Type u) [Field k] (L : Type v) [Field L]
    [Algebra (LaurentSeries k) L] [Algebra (PowerSeries k) L]
    [IsScalarTower (PowerSeries k) (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L] :
    Module.Finite (PowerSeries k) (integralClosure (PowerSeries k) L) :=
  PowerSeries.finite_integralClosure_laurentSeries k L

example (k : Type u) [Field k] (L : Type v) [Field L]
    [Algebra (LaurentSeries k) L] [Algebra (PowerSeries k) L]
    [IsScalarTower (PowerSeries k) (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L] :
    IsDedekindDomain (integralClosure (PowerSeries k) L) :=
  PowerSeries.isDedekindDomain_integralClosure_laurentSeries k L

-- Explicitly admit the purely inseparable auxiliary case which the old route excluded.
example (k : Type u) [Field k] (L : Type v) [Field L]
    [Algebra (LaurentSeries k) L] [Algebra (PowerSeries k) L]
    [IsScalarTower (PowerSeries k) (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    [IsPurelyInseparable (LaurentSeries k) L] :
    Module.Finite (PowerSeries k) (integralClosure (PowerSeries k) L) ∧
      IsDedekindDomain (integralClosure (PowerSeries k) L) :=
  ⟨PowerSeries.finite_integralClosure_laurentSeries k L,
    PowerSeries.isDedekindDomain_integralClosure_laurentSeries k L⟩
