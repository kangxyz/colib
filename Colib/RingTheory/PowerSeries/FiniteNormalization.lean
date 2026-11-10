/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.RingTheory.Nagata.PowerSeries
public import StacksFrontier.RingTheory.Nagata.Examples
public import StacksFrontier.RingTheory.Nagata.Shrink
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.LaurentSeries

/-!
# Finite normalization of the actual power-series DVR

The normalization of `PowerSeries k` in any finite extension of its actual
Laurent-series fraction field is finite, even when that auxiliary extension is
inseparable. The native Japanese-ring theorem supplies finiteness; the native
integral closure is then Dedekind. No field or normalization carrier is replaced.

This is a lower prerequisite for auxiliary descent, not a Milnor norm-residue
square or an assertion that an arbitrary auxiliary extension is unramified.
-/

@[expose] public noncomputable section

universe u v

namespace PowerSeries

/-- A field's actual power-series ring is Japanese in every characteristic. -/
theorem isJapaneseRing_of_field (k : Type u) [Field k] :
    IsJapaneseRing (PowerSeries k) := by
  apply PowerSeries.isJapaneseRing
  exact MonogenicN1.isJapaneseRing_of_isNagataRing IsNagataRing.of_field

/-- The actual power-series normalization is finite for an arbitrary finite
Laurent-field extension. Auxiliary separability is not required. -/
theorem finite_integralClosure_laurentSeries (k : Type u) [Field k]
    (L : Type v) [Field L] [Algebra (LaurentSeries k) L]
    [Algebra (PowerSeries k) L] [IsScalarTower (PowerSeries k) (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L] :
    Module.Finite (PowerSeries k) (integralClosure (PowerSeries k) L) :=
  module_finite_integralClosure_of_isJapaneseRing (isJapaneseRing_of_field k)
    (LaurentSeries k) L

/-- The same native integral closure is Dedekind, including inseparable finite
auxiliary extensions of the Laurent field. -/
theorem isDedekindDomain_integralClosure_laurentSeries (k : Type u) [Field k]
    (L : Type v) [Field L] [Algebra (LaurentSeries k) L]
    [Algebra (PowerSeries k) L] [IsScalarTower (PowerSeries k) (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L] :
    IsDedekindDomain (integralClosure (PowerSeries k) L) := by
  let A := integralClosure (PowerSeries k) L
  let : Module.Finite (PowerSeries k) A := finite_integralClosure_laurentSeries k L
  let : IsNoetherianRing A := IsNoetherianRing.of_finite (PowerSeries k) A
  let : IsFractionRing A L :=
    integralClosure.isFractionRing_of_finite_extension (LaurentSeries k) L
  let : Ring.DimensionLEOne A := Ring.DimensionLEOne.of_isIntegral (PowerSeries k) A
  apply (isDedekindDomain_iff A L).mpr
  exact ⟨inferInstance, inferInstance, inferInstance, fun {x} hx =>
    ⟨IsIntegralClosure.mk' A x (isIntegral_trans (R := PowerSeries k) x hx),
      IsIntegralClosure.algebraMap_mk' A x _⟩⟩

end PowerSeries
