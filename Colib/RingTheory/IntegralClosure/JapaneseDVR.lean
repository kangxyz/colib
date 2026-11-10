/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import StacksFrontier.RingTheory.Nagata.Shrink
public import StacksFrontier.RingTheory.Nagata.Polynomial
public import StacksFrontier.RingTheory.Nagata.Examples

/-!
# Finite normalization for a Japanese DVR and polynomial local rings

The literal integral closure in every finite fraction-field extension is finite
and Dedekind, including inseparable auxiliary extensions. Localizations of the
polynomial ring of an arbitrary field are Japanese. No separability of a closed
point or of an auxiliary field is assumed.
-/

@[expose] public noncomputable section

universe u v w

namespace IsDiscreteValuationRing

/-- Every finite fraction-field extension of a Japanese DVR has its actual
Dedekind normalization, including inseparable extensions. -/
theorem isDedekindDomain_integralClosure_of_isJapaneseRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : IsJapaneseRing R)
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (K : Type w) [Field K] [Algebra F K] [Algebra R K]
    [IsScalarTower R F K] [FiniteDimensional F K] :
    IsDedekindDomain (integralClosure R K) := by
  let A := integralClosure R K
  let : Module.Finite R A := module_finite_integralClosure_of_isJapaneseRing hR F K
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension F K
  let : Ring.DimensionLEOne A := Ring.DimensionLEOne.of_isIntegral R A
  apply (isDedekindDomain_iff A K).mpr
  exact ⟨inferInstance, inferInstance, inferInstance, fun {x} hx =>
    ⟨IsIntegralClosure.mk' A x (isIntegral_trans (R := R) x hx),
      IsIntegralClosure.algebraMap_mk' A x _⟩⟩

end IsDiscreteValuationRing

namespace Polynomial

/-- A polynomial local ring over any field is Japanese; its closed point can
be inseparable over the coefficient field. -/
theorem isJapaneseRing_localizationAtPrime_of_field
    (k : Type u) [Field k] (P : Ideal k[X]) [P.IsPrime] :
    IsJapaneseRing (Localization.AtPrime P) := by
  have hk : IsJapaneseRing k :=
    MonogenicN1.isJapaneseRing_of_isNagataRing IsNagataRing.of_field
  have hpoly : IsJapaneseRing k[X] :=
    (Polynomial.isN1_and_isJapaneseRing k).2 inferInstance hk
  exact (isN1_and_isJapaneseRing_of_isLocalization P.primeCompl
    (Localization.AtPrime P)).2 hpoly

end Polynomial

end
