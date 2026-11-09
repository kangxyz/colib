/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed

/-! Compiled permanent bindings, exact source locators and all public transitive axioms. -/
open Lean Elab Command in
run_cmd do
  let declarations : List Name := [
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassModelSquare,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassModelSquareMap,
  ``AlgebraicGeometry.Scheme.Modules.laurentSquareMap_right_right,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassModelSquare_source,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquareMap,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassCone,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassConeMap,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare_source,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy_naturality_apply,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy_apply,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy_start_naturality,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy_end_naturality,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy_naturality,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_naturality,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassFunctor_eq,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeed,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeed_app,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_apply,
  ``KTheory.Bass.strictRingDiagramFunctor,
  ``KTheory.Bass.strictRingDiagramIterate,
  ``KTheory.Bass.strictRingDiagramTransition,
  ``KTheory.Bass.strictRingDiagramTransition_naturality,
  ``KTheory.Bass.strictRingDiagramSeed,
  ``KTheory.Bass.strictRingDiagramSeed_app,
  ``CommRingCat.PolynomialLaurent.coefficient_toLaurent,
  ``CommRingCat.PolynomialLaurent.coefficient_toLaurent_invert,
  ``CommRingCat.PolynomialLaurent.polynomial_coefficient_square,
  ``CommRingCat.PolynomialLaurent.toLaurent_naturality,
  ``CommRingCat.PolynomialLaurent.invert_naturality,
  ``CommRingCat.PolynomialLaurent.inverseChart_naturality,
  ``CommRingCat.PolynomialLaurent.laurentSquare,
  ``CommRingCat.PolynomialLaurent.laurentSquareMap,
  ``CommRingCat.PolynomialLaurent.laurentSquareFunctor]
  for decl in declarations do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let citations := Colib.Library.citations env
  let endpoints : List (Name × String × String) := [
    (``CommRingCat.PolynomialLaurent.laurentSquare,
      "aglib",
      "Aglib/Algebra/Polynomial/Laurent/Square.lean:40-101"),
    (``CommRingCat.PolynomialLaurent.laurentSquareMap,
      "aglib",
      "Aglib/Algebra/Polynomial/Laurent/Square.lean:40-101"),
    (``CommRingCat.PolynomialLaurent.laurentSquareFunctor,
      "aglib",
      "Aglib/Algebra/Polynomial/Laurent/Square.lean:40-101"),
    (``CommRingCat.PolynomialLaurent.coefficient_toLaurent,
      "aglib",
      "Aglib/Algebra/Polynomial/Laurent/Square.lean:40-101"),
    (``CommRingCat.PolynomialLaurent.coefficient_toLaurent_invert,
      "aglib",
      "Aglib/Algebra/Polynomial/Laurent/Square.lean:40-101"),
    (``KTheory.Bass.strictRingDiagramFunctor,
      "quillen",
      "Quillen/KTheory/Bass/StrictRingDiagram.lean:25-50"),
    (``KTheory.Bass.strictRingDiagramIterate,
      "quillen",
      "Quillen/KTheory/Bass/StrictRingDiagram.lean:25-50"),
    (``KTheory.Bass.strictRingDiagramTransition,
      "quillen",
      "Quillen/KTheory/Bass/StrictRingDiagram.lean:25-50"),
    (``KTheory.Bass.strictRingDiagramTransition_naturality,
      "quillen",
      "Quillen/KTheory/Bass/StrictRingDiagram.lean:25-50"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare,
      "quillen",
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:33-63"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare_source,
      "quillen",
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:33-63"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy,
      "quillen",
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:66-116"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap,
      "quillen",
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:66-116"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_naturality,
      "quillen",
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:66-116"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeed,
      "quillen",
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:119-141"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_apply,
      "quillen",
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:119-141")]
  for (decl, source, locator) in endpoints do
    unless citations.any (fun c => c.declName == decl && c.source == source &&
        c.locator == locator && c.relation == "adaptation") do
      throwError "Missing precise compiled citation for {decl}"
  for decl in [
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare_source,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_naturality,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeed,
  ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_apply] do
    unless (Colib.Library.bindings env).any (fun b =>
        b.declName == decl && b.id == "COL-0361") do
      throwError "Missing compiled COL-0361 binding for {decl}"
