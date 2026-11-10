/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedEvaluationSpectrum
import Lean.Util.CollectAxioms

/-! Audit the actual supported comparison declarations, exact citations, and library bindings. -/
open AlgebraicGeometry.Scheme.Modules
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let citations := Colib.Library.citations env
  let group0 : List Name := [
    ``boundedAboveFlatPerfectSupported,
    ``boundedAboveFlatPerfectSupported_containsZero,
    ``boundedAboveFlatPerfectSupported_closedUnderIsomorphisms,
    ``boundedAboveFlatPerfectSupported_extensionClosed,
    ``boundedAboveFlatPerfectSupported_closedUnderFiniteProducts]
  for decl in group0 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
          Support.lean:39-62") do
      throwError "Missing exact compiled citation for {decl}"
  let group1 : List Name := [
    ``boundedAboveFlatPerfectSupportedWaldhausen,
    ``boundedAboveFlatPerfectSupportedWaldhausen_cof_iff,
    ``boundedAboveFlatPerfectSupportedWaldhausen_weq_iff]
  for decl in group1 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
          SupportComparison.lean:45-48") do
      throwError "Missing exact compiled citation for {decl}"
  let group2 : List Name := [
    ``boundedAboveFlatAffineSectionSupported,
    ``BoundedAboveFlatAffineSupportedSections,
    ``boundedAboveFlatAffineSupportedEvaluation,
    ``boundedAboveFlatAffineSupportedEvaluation_obj]
  for decl in group2 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
          SupportedSections.lean:33-55") do
      throwError "Missing exact compiled citation for {decl}"
  let group3 : List Name := [
    ``boundedAboveFlatAffineSupportedEvaluation_property,
    ``boundedAboveFlatAffineSupportedSectionEquivalence,
    ``boundedAboveFlatAffineSupportedSectionEquivalence_functor,
    ``boundedAboveFlatAffineSupportedEvaluation_isEquivalence,
    ``boundedAboveFlatAffineSupportedEvaluationCounit]
  for decl in group3 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
          SupportedSectionEquivalence.lean:28-65") do
      throwError "Missing exact compiled citation for {decl}"
  let group4 : List Name := [
    ``boundedAboveFlatAffineSectionZero_supported,
    ``boundedAboveFlatAffineSupportedSectionZero,
    ``isZero_boundedAboveFlatAffineSupportedSectionZero]
  for decl in group4 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
          SupportedSectionZero.lean:31-49") do
      throwError "Missing exact compiled citation for {decl}"
  let group5 : List Name := [
    ``boundedAboveFlatAffineSupportedEvaluation_sectionZero_isZero,
    ``boundedAboveFlatAffineSupportedSectionWaldhausen,
    ``boundedAboveFlatAffineSupportedSectionWaldhausen_zero,
    ``boundedAboveFlatAffineSupportedSectionWaldhausen_cof_iff,
    ``boundedAboveFlatAffineSupportedSectionWaldhausen_weq_iff,
    ``boundedAboveFlatAffineSupportedEvaluation_exact,
    ``boundedAboveFlatAffineSupportedSectionEquivalence_inverse_exact]
  for decl in group5 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
          SupportedSectionWaldhausen.lean:34-90") do
      throwError "Missing exact compiled citation for {decl}"
  let group6 : List Name := [
    ``boundedAboveFlatAffineSupportedSectionSmallEquivalence,
    ``boundedAboveFlatAffineSupportedSectionSmallEquivalence_exact,
    ``boundedAboveFlatAffineSupportedSectionSmallEquivalence_inverse_exact,
    ``boundedAboveFlatAffineSupportedSectionEvaluationNormalizationIso,
    ``boundedAboveFlatAffineSupportedSectionNormalizedEquivalence,
    ``boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact,
    ``boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact,
    ``boundedAboveFlatAffineSupportedSectionEvaluationModelMap,
    ``boundedAboveFlatAffineSupportedSectionEvaluationModelIso,
    ``boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap,
    ``boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero]
  for decl in group6 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
          SupportedSectionComparison.lean:35-120") do
      throwError "Missing exact compiled citation for {decl}"
  let group7 : List Name := [
    ``boundedAboveFlatAffineSupportedSectionEvaluationInverseModelMap,
    ``boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy,
    ``boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLevelEquiv,
    ``boundedAboveFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence,
    ``boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_zero,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_one,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_point,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_comm,
    ``boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_zero,
    ``boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_one,
    ``boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_point,
    ``boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_comm]
  for decl in group7 do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
          SupportedSectionSpectrumEquivalence.lean:31-109") do
      throwError "Missing exact compiled citation for {decl}"
  for ax in ← collectAxioms ``boundedAboveFlatAffineSupportedSectionModel do
    unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
      throwError "Unexpected model axiom {ax}"
  unless citations.any (fun c =>
      c.declName == ``boundedAboveFlatAffineSupportedSectionModel && c.source == "quillen" &&
      c.locator == "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
        SupportedSectionModel.lean:32-33") do
    throwError "Missing exact supported model citation"
  let tagged : List Name := [
    ``boundedAboveFlatAffineSupportedSectionEquivalence,
    ``boundedAboveFlatAffineSupportedSectionWaldhausen,
    ``boundedAboveFlatAffineSupportedSectionEvaluationNormalizationIso,
    ``boundedAboveFlatAffineSupportedSectionEvaluationModelMap,
    ``boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy,
    ``boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy,
    ``boundedAboveFlatAffineSupportedSectionEvaluationLevelEquiv,
    ``boundedAboveFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence,
    ``boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence]
  let bindings := (Colib.Library.bindings env).filter (fun b => b.id == "COL-0380")
  unless bindings.size == tagged.length do
    throwError "Unexpected COL-0380 binding count {bindings.size}"
  for decl in tagged do
    unless bindings.any (fun b => b.declName == decl) do
      throwError "Missing COL-0380 binding for {decl}"
  logInfo "Checked supported evaluation axiom closures, exact citations and bindings"
