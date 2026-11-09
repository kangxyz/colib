/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Irreducibility of actual constant polynomials over power and Laurent series

A monic irreducible polynomial over the original coefficient field remains
irreducible over the actual power-series ring and its Laurent-series fraction
field. Its literal reduction under the existing residue-field equivalence is
the original polynomial. These are the inputs for the native monic irreducible
residue AdjoinRoot DVR, without a new constant-closure carrier.

The first two proofs adapt PowerSeriesConstantClosure.lean:28-44 in kangxyz/aglib
at 52e09db47998f139064acf48a2d3a64494d0dd9a, using actual polynomials instead of
its separate MonicIrreducible type. No norm or closure model is introduced.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

variable {k : Type*} [Field k]

/-- A monic irreducible polynomial stays irreducible over the actual power series. -/
theorem Polynomial.Monic.irreducible_map_powerSeries_C {p : k[X]} (hp : p.Monic)
    (hirr : Irreducible p) :
    Irreducible (p.map (PowerSeries.C : k →+* PowerSeries k)) := by
  apply (hp.map _).irreducible_of_irreducible_map
    (φ := PowerSeries.constantCoeff) _
  have hc : PowerSeries.constantCoeff.comp (PowerSeries.C : k →+* PowerSeries k) =
      RingHom.id k := by
    ext x
    simp
  simpa only [Polynomial.map_map, hc, Polynomial.map_id] using hirr

/-- Gauss's lemma applies to the actual Laurent-series fraction field. -/
theorem Polynomial.Monic.irreducible_map_laurentSeries_C {p : k[X]} (hp : p.Monic)
    (hirr : Irreducible p) :
    Irreducible (p.map (algebraMap k (LaurentSeries k))) := by
  have h := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := LaurentSeries k) (hp.map (PowerSeries.C : k →+* PowerSeries k))).mp
      (hp.irreducible_map_powerSeries_C hirr)
  have hc : (algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (PowerSeries.C : k →+* PowerSeries k) = algebraMap k (LaurentSeries k) := rfl
  simpa only [Polynomial.map_map, hc] using h

/-- The literal residue polynomial becomes the original polynomial under the
existing native power-series residue-field equivalence. -/
theorem Polynomial.map_powerSeries_C_residueFieldOfPowerSeries (p : k[X]) :
    (((p.map (PowerSeries.C : k →+* PowerSeries k)).map (residue (PowerSeries k))).map
      PowerSeries.residueFieldOfPowerSeries.toRingHom) = p := by
  have hc : PowerSeries.residueFieldOfPowerSeries.toRingHom.comp
      ((residue (PowerSeries k)).comp (PowerSeries.C : k →+* PowerSeries k)) =
      RingHom.id k := by
    ext x
    change PowerSeries.constantCoeff (PowerSeries.C x) = x
    simp
  simp only [Polynomial.map_map, hc, Polynomial.map_id]

/-- The actual power-series residue reduction is irreducible, so the native
AdjoinRoot irreducible-reduction DVR theorems apply directly. -/
theorem Polynomial.Monic.irreducible_map_powerSeries_C_residue {p : k[X]} (hp : p.Monic)
    (hirr : Irreducible p) :
    Irreducible ((p.map (PowerSeries.C : k →+* PowerSeries k)).map
      (residue (PowerSeries k))) := by
  apply ((hp.map _).map _).irreducible_of_irreducible_map
    (φ := PowerSeries.residueFieldOfPowerSeries.toRingHom) _
  simpa only [Polynomial.map_powerSeries_C_residueFieldOfPowerSeries] using hirr
