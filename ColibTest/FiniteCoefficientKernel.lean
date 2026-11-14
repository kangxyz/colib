/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Kernel

/-! # Regression checks for the canonical kernel finite-coefficient comparison -/

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

example (G : C) : QuasiIso (finiteCoefficients.fromKernelSingle G 1) := by
  have : Epi (1 • 𝟙 G) := by simpa using (inferInstance : Epi (𝟙 G))
  exact finiteCoefficients.quasiIso_fromKernelSingle G 1

example (G : C) [Epi (6 • 𝟙 G)] : QuasiIso (finiteCoefficients.fromKernelSingle G 6) :=
  finiteCoefficients.quasiIso_fromKernelSingle G 6

example (G : C) [Epi (0 • 𝟙 G)] : QuasiIso (finiteCoefficients.fromKernelSingle G 0) :=
  finiteCoefficients.quasiIso_fromKernelSingle G 0


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let primary := ``finiteCoefficients.kernelSingleFiniteIso
  for decl in [primary, ``finiteCoefficients.kernelSingleFiniteIso_naturality,
      ``mappingCone.fromShortComplex_bockstein] do
    unless (Colib.Library.bindings env).any (fun b =>
        b.id == "COL-1234" && b.declName == decl) do
      throwError "Missing compiled COL-1234 binding for {decl}"
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    let refs := (Colib.Library.citations env).filter (fun c => c.declName == decl)
    let expected := if decl == primary then 2 else 1
    unless refs.size == expected do
      throwError "Expected {expected} references for {decl}, got {refs.size}"
    for citation in refs do
      logInfo m!"COL1234_REF|{citation.source}|{citation.locator}"
