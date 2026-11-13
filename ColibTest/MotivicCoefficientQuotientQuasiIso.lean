/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientQuotientQuasiIso

/-! # Boundary regressions for the original motivic coefficient model -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

example (q : ℕ) : QuasiIso (motivicFiniteToCoefficientQuotient k q 1) :=
  motivicFiniteToCoefficientQuotient_quasiIso k q 1 (by decide)

example (n : ℕ) (hn : n ≠ 0) : QuasiIso (motivicFiniteToCoefficientQuotient k 0 n) :=
  motivicFiniteToCoefficientQuotient_quasiIso k 0 n hn

example (q : ℕ) : QuasiIso (motivicFiniteToCoefficientQuotient k q 6) :=
  motivicFiniteToCoefficientQuotient_quasiIso k q 6 (by decide)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let primary := ``motivicFiniteToCoefficientQuotient_quasiIso
  unless (Colib.Library.bindings env).any (fun b =>
      b.id == "COL-1229" && b.declName == primary) do
    throwError "Missing compiled COL-1229 binding"
  unless (Colib.Library.citations env).any (fun c =>
      c.declName == primary && c.source == "mathlib_stable_localization_pin" &&
      c.locator == "Mathlib/Algebra/Homology/HomotopyCategory/ShortExact.lean:138-154") do
    throwError "Missing precise native mapping-cone reference"
  for decl in [primary, ``motivicFiniteToCoefficientModuleComplex_quasiIso,
      ``reducedTorusSection_quotient] do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
