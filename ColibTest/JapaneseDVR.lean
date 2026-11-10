/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.IntegralClosure.JapaneseDVR

noncomputable section

open Polynomial

universe u v w

example (k : Type u) [Field k] (P : Ideal k[X]) [P.IsPrime] :
    IsJapaneseRing (Localization.AtPrime P) :=
  Polynomial.isJapaneseRing_localizationAtPrime_of_field k P

example (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : IsJapaneseRing R)
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (K : Type w) [Field K] [Algebra F K] [Algebra R K]
    [IsScalarTower R F K] [FiniteDimensional F K] :
    IsDedekindDomain (integralClosure R K) :=
  IsDiscreteValuationRing.isDedekindDomain_integralClosure_of_isJapaneseRing R hR F K

example (k : Type u) [Field k] (P : Ideal k[X]) [P.IsPrime]
    (F : Type v) [Field F] [Algebra (Localization.AtPrime P) F]
    [IsFractionRing (Localization.AtPrime P) F]
    (K : Type w) [Field K] [Algebra F K] [Algebra (Localization.AtPrime P) K]
    [IsScalarTower (Localization.AtPrime P) F K] [FiniteDimensional F K] :
    Module.Finite (Localization.AtPrime P) (integralClosure (Localization.AtPrime P) K) :=
  module_finite_integralClosure_of_isJapaneseRing
    (Polynomial.isJapaneseRing_localizationAtPrime_of_field k P) F K

end
