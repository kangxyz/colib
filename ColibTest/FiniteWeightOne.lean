/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneSheafComparison
import Colib.AlgebraicGeometry.Sites.Smooth.Units.EtaleSheaf

/-! # Regression checks for the actual finite weight-one comparison -/

open CategoryTheory AlgebraicGeometry

universe u

example (k : Type u) [Field k] :
    QuasiIso (MotivicCohomology.WeightOne.weightOneFiniteSheafComparison k 0) :=
  MotivicCohomology.WeightOne.weightOneFiniteSheafComparison_quasiIso k 0

example (k : Type u) [Field k] :
    QuasiIso (MotivicCohomology.WeightOne.weightOneFiniteSheafComparison k 6) :=
  MotivicCohomology.WeightOne.weightOneFiniteSheafComparison_quasiIso k 6

#print axioms CochainComplex.finiteCoefficients.quasiIso_map
#print axioms MotivicCohomology.WeightOne.weightOneCoefficientQuotientUnitsIso
#print axioms Scheme.SmoothSite.unitsPresheaf_isSheaf_etale

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let primary := ``MotivicCohomology.WeightOne.weightOneCoefficientQuotientUnitsIso
  unless (Colib.Library.bindings env).any (fun b =>
      b.id == "COL-1231" && b.declName == primary) do
    throwError "Missing compiled COL-1231 binding"
  unless (Colib.Library.citations env).any (fun c =>
      c.declName == primary && c.source == "mathlib_stable_localization_pin" &&
      c.locator == "Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:514-517") do
    throwError "Missing native two-out-of-three reference"
  for decl in [primary, ``CochainComplex.finiteCoefficients.quasiIso_map,
      ``Scheme.SmoothSite.unitsPresheaf_isSheaf_etale] do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
