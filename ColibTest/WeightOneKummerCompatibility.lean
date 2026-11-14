/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public meta import Batteries.Tactic.Lint
import all Colib.Algebra.Homology.DerivedCategory.KernelBoundaryDegreeOne
import all Colib.Algebra.Homology.DerivedCategory.ProjectiveRepresentatives
import all Colib.Algebra.Homology.DerivedCategory.ProjectiveSingleCoordinate
import all Colib.Algebra.Homology.DerivedCategory.SingleSourceTransport
import all Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceEquality
import all Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceSections
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.IntegralReductionDerived
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.MilnorKummerCompatibility
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneBaseSource
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallCanonicalSource
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallSource
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralBaseSource
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralBoundary
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralKummerComparison
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralSource
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneKummerCompatibility
import all Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneTopologySource
import all Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.ComparisonPostcompose
import all Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.NormSections
import all Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SourceCoordinates
import all Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestrictionAtBaseNaturality
import all Colib.CategoryTheory.Sites.TerminalCohomologyDegreeOne

/-! Diagnostic aggregate import, exact Library bindings, axiom audit, and selected-module lint. -/
open Lean Elab Command
open AlgebraicGeometry.MotivicCohomology.WeightOne
set_option maxHeartbeats 1600000 in
-- Run all registered environment linters sequentially over the reconstructed module declarations.
run_cmd do
  let env ← getEnv
  let finals := #[
    ``weightOneFiniteEtaleCohomologyMap_integral_unitKummerClass,
    ``weightOneFiniteEtaleCohomologyMap_integral_norm,
    ``weightOneFiniteEtaleCohomologyMap_motivicFiniteEquiv]
  for decl in finals do
    unless (Colib.Library.bindings env).any (fun b =>
        b.id == "COL-1231" && b.declName == decl) do
      throwError "Missing COL-1231 binding for {decl}"
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless ((Colib.Library.citations env).filter (·.declName == decl)).size == 1 do
      throwError "Expected exactly one citation for {decl}"
  unless (Colib.Library.bindings env).any (fun b =>
      b.id == "COL-1227" && b.declName == finals[2]!) do
    throwError "Missing COL-1227 final comparison binding"
  let selected : Array Name := #[
    `Colib.Algebra.Homology.DerivedCategory.KernelBoundaryDegreeOne,
    `Colib.Algebra.Homology.DerivedCategory.ProjectiveRepresentatives,
    `Colib.Algebra.Homology.DerivedCategory.ProjectiveSingleCoordinate,
    `Colib.Algebra.Homology.DerivedCategory.SingleSourceTransport,
    `Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceEquality,
    `Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceSections,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.IntegralReductionDerived,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.MilnorKummerCompatibility,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneBaseSource,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallCanonicalSource,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallSource,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralBaseSource,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralBoundary,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralKummerComparison,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralSource,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneKummerCompatibility,
    `Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneTopologySource,
    `Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.ComparisonPostcompose,
    `Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.NormSections,
    `Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SourceCoordinates,
    .str `Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale
      "DerivedRestrictionAtBaseNaturality",
    `Colib.CategoryTheory.Sites.TerminalCohomologyDegreeOne]
  let modules := env.header.moduleNames.map (selected.contains ·)
  let decls := env.constants.map₁.fold (init := #[]) fun ds decl _ =>
    if modules[env.const2ModIdx[decl]?.get!]! then ds.push decl else ds
  let checks ← liftCoreM <| Batteries.Tactic.Lint.getChecks (slow := true) none none
  let mut failures : Nat := 0
  for check in checks do
    for decl in decls do
      if ← liftCoreM (Batteries.Tactic.Lint.shouldBeLinted check.name decl) then
        if let some message ← liftTermElabM fun _ => check.test decl then
          failures := failures + 1
          logError m!"{check.name}: {decl}: {message}"
  logInfo m!"AUDIT: bindings, native axioms, {decls.size} declarations, \
    {checks.size} linters, {failures} findings"
