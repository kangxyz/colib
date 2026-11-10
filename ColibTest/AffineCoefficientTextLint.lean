/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Mathlib.Tactic.Linter.TextBased

/-! Check every owned production and test file with the unchanged native text linters. -/
open Lean Elab Command Mathlib.Linter.TextBased in
run_cmd do
  let modules : Array Name := #[
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoherence,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompAssociation,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompPasting,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompRelative,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplit,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplitRelative,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompTracks,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationComponents,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationIsoConstructors,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationModelCoherence,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationPerfect,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationRawSource,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationSourceTransport,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationUnitRoutes,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineGeometricCompositionLevels,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineGeometricIsoConstructor,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineNormalizationSplit,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffinePullbackCompTotalSplit,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffinePullbackModelConstructor,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition,
    `Colib.CategoryTheory.Functor.TransportIso,
    `Colib.KTheory.Waldhausen.AsSmall.ComparisonIso,
    `Colib.KTheory.Waldhausen.AsSmall.TransportComparisonIso,
    `Colib.KTheory.Waldhausen.Iterated.IsoHomotopyCongruence,
    `Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumIdentityHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedIteratedLevels,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedTransformationLevels,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumPastingHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.PrespectrumUnitHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelComparisonIso,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelCompositionHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationCoherence,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationComparison,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelNativeNormalizationCompositionHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelNormalizationCompositionHomotopy,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelTransformationIso,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelTransformations,
    `Colib.KTheory.Waldhausen.Iterated.SmallModelWhiskering,
    `Colib.KTheory.Waldhausen.Iterated.SmallSourceEvaluationComparison,
    `Colib.Topology.Prespectrum.HomotopyNamedCastLevels,
    `Colib.Topology.Prespectrum.HomotopyNamedDoubleCastLevels,
    `Colib.Topology.Prespectrum.HomotopyNamedLevels,
    `Colib.Topology.Prespectrum.HomotopySourceTransport,
    `Colib.Topology.Prespectrum.RelativeHomotopySourceTransport,
    `ColibTest.AffineCoefficientFormulas,
    `ColibTest.AffineCoefficientLibraryExport,
    `ColibTest.AffineCompWholeLevels,
    `ColibTest.AffineOriginalSplitEndpoints,
    `ColibTest.AffineOriginalSplitNonflat,
    `ColibTest.AffineOriginalSplitStructure,
    `ColibTest.AffinePerfectEvaluationFormulas,
    `ColibTest.AffinePerfectFlatCoefficient,
    `ColibTest.AffinePerfectRelativeStructures,
    `ColibTest.AffineTotalSplitEndpoints,
    `ColibTest.AffineTotalSplitNonflat,
    `ColibTest.AffineTotalSplitStructure,
    `ColibTest.AffineTotalSplitWholeLevels,
    `ColibTest.AffineUnitEndpoints,
    `ColibTest.AffineUnitStructure,
    `ColibTest.AffineUnitWholeLevels,
    `ColibTest.AffineCoefficientTextLint]
  let opts ← Lean.Linter.getLinterOptions
  unless (← lintModules opts #[] modules .humanReadable false) == 0 do
    throwError "Pinned native text lint failed"
  unless (← modulesNotUpperCamelCase opts modules) == 0 do
    throwError "Native module casing lint failed"
  unless (← modulesOSForbidden opts modules) == 0 do
    throwError "Native module filename lint failed"
  logInfo "PASS: native text and module-name lint for all 46 production and 17 test files"
