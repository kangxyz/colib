/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplitRelative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationUnitRoutes
public import Colib.Topology.Prespectrum.HomotopySourceTransport
import Lean.Util.CollectAxioms

/-! Self-attributed compiled endpoints and the production dependency axiom closure. -/
open AlgebraicGeometry.Scheme.Modules

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let endpoints : List Name := [
    ``boundedAboveFlatAffineEvaluationCoefficientHomotopy,
    ``boundedAboveFlatAffineEvaluationKEquiv_naturality,
    ``boundedAboveFlatAffinePerfectEvaluationMap_isStableEquivalence,
    ``boundedAboveFlatAffinePerfectEvaluationKEquiv_zeroSpace,
    ``boundedAboveFlatAffinePerfectEvaluationKEquiv_stable,
    ``boundedAboveFlatAffinePerfectFlatCoefficientHomotopy,
    ``boundedAboveFlatAffinePerfectEvaluationKEquiv_naturality,
    ``boundedAboveFlatAffineEvaluationCompSplitRelHomotopy,
    ``boundedAboveFlatAffineEvaluationUnitRelHomotopy]
  let bindings := (Colib.Library.bindings env).filter (fun b => b.id == "COL-0381")
  unless bindings.size == 9 do
    throwError "Expected exactly nine own affine coefficient bindings, got {bindings.size}"
  for name in endpoints do
    unless bindings.any (fun b => b.declName == name) do
      throwError "Missing own affine binding {name}"
    unless (Colib.Library.citations env).any (fun c => c.declName == name &&
        c.source == "quillen" && !c.locator.isEmpty && !c.scope.isEmpty) do
      throwError "Missing self-attributed implementation reference for {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected endpoint axiom {ax} in {name}"
  let modules : List Name := [
    `Colib.CategoryTheory.Functor.TransportIso,
    `Colib.KTheory.Waldhausen.AsSmall.ComparisonIso,
    `Colib.KTheory.Waldhausen.AsSmall.TransportComparisonIso,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumIdentityHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumPastingHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelComparisonIso,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationCoherence,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationComparison,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelTransformations,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelWhiskering,
    `Colib.KTheory.Waldhausen.Iterated.SmallSourceEvaluationComparison,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoherence,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompPasting,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompTracks,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationComponents,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationIsoConstructors,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationModelCoherence,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationPerfect,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationRawSource,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationSourceTransport,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineGeometricIsoConstructor,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineNormalizationSplit,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition,
    `Colib.KTheory.Waldhausen.Iterated.IsoHomotopyCongruence,
    `Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumUnitHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelCompositionHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelNormalizationCompositionHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelTransformationIso,
    `Colib.Topology.Prespectrum.HomotopySourceTransport,
    `Colib.Topology.Prespectrum.RelativeHomotopySourceTransport,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineGeometricCompositionLevels,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffinePullbackModelConstructor,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelNativeNormalizationCompositionHomotopy,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffinePullbackCompTotalSplit,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplit,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompAssociation,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedTransformationLevels,
    `Colib.Topology.Prespectrum.HomotopyNamedLevels,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedIteratedLevels,
    `Colib.Topology.Prespectrum.HomotopyNamedCastLevels,
    `Colib.Topology.Prespectrum.HomotopyNamedDoubleCastLevels,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompRelative,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplitRelative,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationUnitRoutes]
  unless modules.length == 46 && modules.eraseDups.length == 46 do
    throwError "Expected exactly 46 distinct production owners"
  let constants := env.constants
  let indices := env.const2ModIdx
  let mut checked : Nat := 0
  let mut ownerCounts : Array Json := #[]
  for owner in modules do
    let some i := env.getModuleIdx? owner |
      throwError "Expected production owner is not loaded: {owner}"
    let some data := env.header.moduleData[i]? |
      throwError "Missing native module data for production owner {owner}"
    unless data.constNames.size == data.constants.size do
      throwError "Invalid native declaration inventory for {owner}"
    let mut names : Array Name := #[]
    for name in data.constNames do
      if (constants.find? name).isSome && indices[name]? == some i then
        names := names.push name
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected production axiom {ax} in {name}"
        checked := checked + 1
    unless !names.isEmpty do
      throwError "No actual declarations found for production owner {owner}"
    ownerCounts := ownerCounts.push <| Json.mkObj [
      ("module", toJson owner.toString), ("count", toJson names.size),
      ("names", toJson (names.map Name.toString))]
  unless checked > 0 do
    throwError "No owned production declarations inspected"
  logInfo m!"Affine coefficient metadata: 9 self-cited bindings; {checked} declarations audited"
  let mut rows := #[]
  for name in endpoints do
    unless (env.find? name).isSome do
      throwError "Missing declaration {name}"
    let some i := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    let axioms ← Lean.collectAxioms name
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson env.header.moduleNames[i]!.toString),
      ("axioms", toJson (axioms.map Name.toString))]
  let ownCitations := (Colib.Library.citations env).filter fun c =>
    endpoints.contains c.declName
  IO.println <| (Json.mkObj [
    ("ownerDeclarations", Json.arr ownerCounts),
    ("auditedDeclarationCount", toJson checked),
    ("declarations", Json.arr rows),
    ("bindings", toJson (endpoints.map Name.toString)),
    ("citations", Json.arr (ownCitations.map fun c => Json.mkObj [
      ("name", toJson c.declName.toString), ("source", toJson c.source),
      ("locator", toJson c.locator), ("relation", toJson c.relation),
      ("scope", toJson c.scope)])) ]).compress
