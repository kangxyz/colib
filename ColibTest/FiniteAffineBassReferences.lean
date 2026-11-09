/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassConeExcision

open AlgebraicGeometry.Scheme.Modules

/-! Verify the complete public axiom closure and precise compiled source correspondence. -/

open Lean Elab Command in
run_cmd do
  let declarations : List Name := [
    ``boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence,
    ``boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence,
    ``boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence,
    ``boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at,
    ``boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le,
    ``boundedAboveFlatAffineSectionBassDiagram_toPoint_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionBassTransition_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty,
    ``boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty,
    ``KTheory.Bass.strictDiagramFunctor_point_homotopyExtensionProperty,
    ``KTheory.Bass.strictDiagramIterate_point_homotopyExtensionProperty,
    ``KTheory.Bass.strictDiagramFunctor_homotopyGroup_subsingleton,
    ``KTheory.Bass.strictDiagramIterate_homotopyGroup_subsingleton,
    ``TopCat.DoubleCylinder.pathConnectedSpace,
    ``TopCat.DoubleCylinder.homotopyGroup_subsingleton,
    ``Topology.ReducedMappingCone.homotopyGroup_subsingleton,
    ``Topology.HomotopyPullback.isHomotopyConnectedMap_of_baseProjection,
    ``Topology.LoopPrespectrum.HomotopyPushout.UnreducedSpace,
    ``Topology.LoopPrespectrum.HomotopyPushout.unreducedCylinder,
    ``Topology.LoopPrespectrum.HomotopyPushout.unreducedEnd,
    ``Topology.LoopPrespectrum.HomotopyPushout.unreducedSquare,
    ``Topology.LoopPrespectrum.HomotopyPushout.reduction,
    ``Topology.LoopPrespectrum.HomotopyPushout.reduction_cylinder,
    ``Topology.LoopPrespectrum.HomotopyPushout.reduction_end,
    ``Topology.LoopPrespectrum.HomotopyPushout.intervalToPoint,
    ``Topology.LoopPrespectrum.HomotopyPushout.reducedPoint,
    ``Topology.LoopPrespectrum.HomotopyPushout.reduction_square,
    ``Topology.LoopPrespectrum.HomotopyPushout.reduction_isPushout,
    ``Topology.LoopPrespectrum.HomotopyPushout.reductionHomotopyEquiv,
    ``Topology.LoopPrespectrum.HomotopyPushout.reductionHomotopyEquiv_toFun,
    ``Topology.LoopPrespectrum.HomotopyPushout.point_homotopyExtensionProperty,
    ``Topology.LoopPrespectrum.HomotopyPushout.homotopyGroup_subsingleton,
    ``Topology.LoopPrespectrum.StrictSquare.span_point_homotopyExtensionProperty,
    ``Topology.LoopPrespectrum.StrictSquare.cone_point_homotopyExtensionProperty,
    ``Topology.LoopPrespectrum.StrictSquare.loopedCone_point_homotopyExtensionProperty,
    ``Topology.LoopPrespectrum.StrictSquare.loopedCone_homotopyGroup_subsingleton]
  for decl in declarations do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let citations := Colib.Library.citations env
  let endpoints : List (Name × String) := [
    (``boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:31"),
    (``boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:58"),
    (``boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:71"),
    (``boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:80"),
    (``boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:28"),
    (``boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:42"),
    (``boundedAboveFlatAffineSectionBassDiagram_toPoint_isHomotopyConnectedMap,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:56"),
    (``boundedAboveFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:67"),
    (``boundedAboveFlatAffineSectionBassTransition_isHomotopyConnectedMap,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:84"),
    (``boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTopology.lean:32"),
    (``boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTopology.lean:46"),
    (``KTheory.Bass.strictDiagramFunctor_point_homotopyExtensionProperty,
      "Quillen/KTheory/Bass/StrictDiagramTopology.lean:37"),
    (``KTheory.Bass.strictDiagramIterate_point_homotopyExtensionProperty,
      "Quillen/KTheory/Bass/StrictDiagramTopology.lean:62"),
    (``KTheory.Bass.strictDiagramFunctor_homotopyGroup_subsingleton,
      "Quillen/KTheory/Bass/StrictDiagramVanishing.lean:27"),
    (``KTheory.Bass.strictDiagramIterate_homotopyGroup_subsingleton,
      "Quillen/KTheory/Bass/StrictDiagramVanishing.lean:53"),
    (``TopCat.DoubleCylinder.pathConnectedSpace,
      "Quillen/Topology/DoubleMappingCylinder/Connectivity.lean:35"),
    (``TopCat.DoubleCylinder.homotopyGroup_subsingleton,
      "Quillen/Topology/DoubleMappingCylinder/Connectivity.lean:65"),
    (``Topology.ReducedMappingCone.homotopyGroup_subsingleton,
      "Quillen/Topology/HomotopyCofiber/ReducedMappingConeVanishing.lean:27"),
    (``Topology.HomotopyPullback.isHomotopyConnectedMap_of_baseProjection,
      "Quillen/Topology/HomotopyPullback/ConnectivityReflection.lean:26-48"),
    (``Topology.LoopPrespectrum.HomotopyPushout.UnreducedSpace,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:32"),
    (``Topology.LoopPrespectrum.HomotopyPushout.unreducedCylinder,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:36"),
    (``Topology.LoopPrespectrum.HomotopyPushout.unreducedEnd,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:40"),
    (``Topology.LoopPrespectrum.HomotopyPushout.unreducedSquare,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:44"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reduction,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:49"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reduction_cylinder,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:60"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reduction_end,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:64"),
    (``Topology.LoopPrespectrum.HomotopyPushout.intervalToPoint,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:69"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reducedPoint,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:73"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reduction_square,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:77"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reduction_isPushout,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:84"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reductionHomotopyEquiv,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:150"),
    (``Topology.LoopPrespectrum.HomotopyPushout.reductionHomotopyEquiv_toFun,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:182"),
    (``Topology.LoopPrespectrum.HomotopyPushout.point_homotopyExtensionProperty,
      "Quillen/Topology/Prespectrum/PushoutReduction.lean:193"),
    (``Topology.LoopPrespectrum.HomotopyPushout.homotopyGroup_subsingleton,
      "Quillen/Topology/Prespectrum/PushoutVanishing.lean:27"),
    (``Topology.LoopPrespectrum.StrictSquare.span_point_homotopyExtensionProperty,
      "Quillen/Topology/Prespectrum/StrictSquareTopology.lean:43"),
    (``Topology.LoopPrespectrum.StrictSquare.cone_point_homotopyExtensionProperty,
      "Quillen/Topology/Prespectrum/StrictSquareTopology.lean:55"),
    (``Topology.LoopPrespectrum.StrictSquare.loopedCone_point_homotopyExtensionProperty,
      "Quillen/Topology/Prespectrum/StrictSquareTopology.lean:71"),
    (``Topology.LoopPrespectrum.StrictSquare.loopedCone_homotopyGroup_subsingleton,
      "Quillen/Topology/Prespectrum/StrictSquareVanishing.lean:28")]
  for (decl, locator) in endpoints do
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == locator && c.relation == "adaptation") do
      throwError "Missing precise compiled citation for {decl}"
  for decl in [
    ``boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence,
    ``boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence,
    ``boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence,
    ``boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at,
    ``boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le,
    ``boundedAboveFlatAffineSectionBassDiagram_toPoint_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionBassTransition_isHomotopyConnectedMap,
    ``boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty,
    ``boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty] do
    unless (Colib.Library.bindings env).any (fun b =>
        b.declName == decl && b.id == "COL-0375") do
      throwError "Missing compiled COL-0375 binding for {decl}"
