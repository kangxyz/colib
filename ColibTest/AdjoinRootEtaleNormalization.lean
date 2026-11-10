/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdjoinRoot.EtaleNormalization
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.DedekindDomain.Basic

open Polynomial

noncomputable section

universe u v w

example {k R : Type*} [CommRing k] [CommRing R] (f : k →+* R)
    {p : k[X]} (hp : p.Monic) (hsep : p.Separable) :
    Module.Finite R (AdjoinRoot (p.map f)) ∧ Algebra.Etale R (AdjoinRoot (p.map f)) :=
  AdjoinRoot.finite_etale_map_of_monic_of_separable f hp hsep

-- Literal constant polynomial, literal power-series coefficient map; arbitrary characteristic.
example {k : Type u} [Field k] {p : k[X]} (hp : p.Monic) (hsep : p.Separable) :
    Module.Finite (PowerSeries k)
        (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) ∧
      Algebra.Etale (PowerSeries k)
        (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.finite_etale_map_of_monic_of_separable _ hp hsep

-- Full generic root algebra, before selecting any field factor.
example {k : Type u} [Field k] {p : k[X]} (hp : p.Monic) (hsep : p.Separable) :
    Module.Finite (PowerSeries k)
        (integralClosure (PowerSeries k)
          (AdjoinRoot ((p.map (PowerSeries.C : k →+* PowerSeries k)).map
            (algebraMap (PowerSeries k) (LaurentSeries k))))) ∧
      Algebra.Etale (PowerSeries k)
        (integralClosure (PowerSeries k)
          (AdjoinRoot ((p.map (PowerSeries.C : k →+* PowerSeries k)).map
            (algebraMap (PowerSeries k) (LaurentSeries k))))) :=
  AdjoinRoot.finite_etale_integralClosure_map_of_separable (PowerSeries k) (LaurentSeries k)
    (hp.map _) hsep.map

-- An actual generic field factor over an arbitrary auxiliary DVR. No separability
-- of that DVR's fraction field over the earlier Laurent field is supplied.
example (k : Type u) [Field k] (R : Type v) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K E : Type w) [Field K] [Field E]
    [Algebra k R] [Algebra R K] [IsFractionRing R K] [Algebra k K]
    [IsScalarTower k R K] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    {p : k[X]} (hp : p.Monic) (hsep : p.Separable)
    (f : AdjoinRoot (p.map (algebraMap k K)) →ₐ[K] E) (hf : Function.Surjective f) :
    Module.Finite R (integralClosure R E) ∧ Algebra.Etale R (integralClosure R E) :=
  AdjoinRoot.finite_etale_integralClosure_constant_factor k R K E hp hsep f hf
