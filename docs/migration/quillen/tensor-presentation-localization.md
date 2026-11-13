# Tensor presentation localization migration

Source: Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

## Final targets

- `ParameterTensorPresentation.basicLift_integer_isStableEquivalence`.
- `ParameterTensorPresentation.auxiliaryLift_integer_isStableEquivalence`.
- Original timewise null comparison and exact fiber-projection maps.

The source hypotheses and actual tensor-normalized presentations are retained.
These are transports of the current-stage localization theorems through the original
ordinary-colimit comparisons, not a replacement model or an independent proof of TT 7.4.

The 24 restored source modules retain the exact original sequence of all 132 declarations.
The two complete original consumer modules are present, alongside the pre-existing examples.

## Source ownership

- `Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationLocalization` → `Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationLocalization`.
- `Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationActions` → `Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationActions`.
- `Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationDiagram` → `Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationDiagram`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialComparisonStable` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialComparisonStable`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialComparison` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialComparison`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialDiagram` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialDiagram`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialInputLaws` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialInputLaws`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialInput` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialInput`.
- `Quillen.Topology.Prespectrum.ZigzagSequentializationColimitNaturality` → `Colib.Topology.Prespectrum.ZigzagSequentializationColimitNaturality`.
- `Quillen.Topology.Prespectrum.SequentialColimitNaturality` → `Colib.Topology.Prespectrum.SequentialColimitNaturality`.
- `Quillen.Topology.Prespectrum.ZigzagSequentializationMapLaws` → `Colib.Topology.Prespectrum.ZigzagSequentializationMapLaws`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialNullTransport` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialNullTransport`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialDiagramNull` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialDiagramNull`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialNull` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialNull`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialHomotopy` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialHomotopy`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialFiniteMap` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialFiniteMap`.
- `Quillen.Topology.Prespectrum.SuspensionLoopHomotopy` → `Colib.Topology.Prespectrum.SuspensionLoopHomotopy`.
- `Quillen.Topology.Prespectrum.ZigzagSequentializationColimitHomotopy` → `Colib.Topology.Prespectrum.ZigzagSequentializationColimitHomotopy`.
- `Quillen.Topology.Prespectrum.ZigzagSequentializationHomotopy` → `Colib.Topology.Prespectrum.ZigzagSequentializationHomotopy`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialLiftTransport` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialLiftTransport`.
- `Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorComparisonChoice` → `Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorComparisonChoice`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialProofChoice` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialProofChoice`.
- `Quillen.KTheory.Bass.SchemeTrackSequentialInitial` → `Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialInitial`.
- `Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationAuxiliary` → `Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationAuxiliary`.

Two declarations omitted from the previously migrated suspension unit closure are
restored from the same pin: `suspensionConeMap` and `suspensionLoopUnit_naturality`.
The original `suspensionLoopUnit_apply` computation is retained as well.

## Validation

Native local compilation passed for both final localization modules and the complete original
`ParameterTensorPresentationLocalization` and `ParameterTensorPresentation` consumers. Existing
ambient/supported examples are retained. The original input parameter `Model` is expressed directly
as the native `WideSubcategory preservesZero`, and the integer base is the actual
`Spec (CommRingCat.of (ULift ℤ))`, without compatibility aliases. All proof changes are ownership,
namespace, explicit qualification or formatting changes; the source selected maps, nulls and
hypotheses are retained. The local closure completed 14,783 Lake jobs on 2026-11-12 using exact
0830fbb8 baseline outputs and fresh compilation for the changed dependency closure.

Library records COL-0599 and COL-0600 give the two final endpoints with their exact model scope.
Full local production compilation also passes (`lake build Colib`, 21,557 jobs).
Catalog validation passes for 524 items and its 102 unit tests. This records source correspondence and Lean validation,
not an independent mathematical review or a new classical comparison.
