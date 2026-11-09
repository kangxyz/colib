/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentHomotopy

/-! Compiled source locators, permanent item bindings and native transitive axioms. -/

open AlgebraicGeometry.Scheme.Modules

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let citations := Colib.Library.citations env
  let endpoints : List (Name × String) := [
    (``boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_apply,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:75-90"),
    (``CategoryTheory.Functor.IdentityAutomorphism.onFunctor_whisker_square,
      "Quillen/Aglib/CategoryTheory/Functor/IdentityAutomorphismSquare.lean:19-33"),
    (``boundedAboveFlatAffineSectionLaurentPullbackUnitIso,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentPullback.lean:26-32"),
    (``boundedAboveFlatAffineSectionLaurentModelSquare,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:33-43"),
    (``boundedAboveFlatAffineSectionLaurentModelUnitSquare,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:51-66"),
    (``boundedAboveFlatAffineSectionLaurentUnitHomotopy,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:68-73")]
  for (decl, locator) in endpoints do
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == locator && c.relation == "adaptation") do
      throwError "Missing precise compiled citation for {decl}"
  for decl in [
      ``boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_apply,
      ``boundedAboveFlatAffineSectionLaurentModelSquare,
      ``boundedAboveFlatAffineSectionLaurentModelUnitSquare,
      ``boundedAboveFlatAffineSectionLaurentUnitHomotopy,
      ``boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality] do
    unless (Colib.Library.bindings env).any (fun b =>
        b.declName == decl && b.id == "COL-0360") do
      throwError "Missing compiled COL-0360 binding for {decl}"

open Lean Elab Command in
run_cmd do
  let declarations : List Name := [
    ``boundedAboveFlatAffineSectionLaurentPullbackUnitIso,
    ``boundedAboveFlatAffineSectionLaurentModelSquare,
    ``boundedAboveFlatAffineSectionLaurentModelUnitSquare,
    ``boundedAboveFlatAffineSectionLaurentUnitHomotopy,
    ``boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_apply,
    ``boundedAboveFlatAffineSectionLaurentPrespectrumSquare,
    ``boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_at,
    ``boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoefficientInclusion,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoefficientInclusion_square,
    ``CategoryTheory.Functor.IdentityAutomorphism.onFunctor_whisker_square]
  for decl in declarations do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
