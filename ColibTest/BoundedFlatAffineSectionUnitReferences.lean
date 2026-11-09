/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionLaurentUnit

/-! Check actual imported citations, item bindings and transitive declaration axioms. -/

open AlgebraicGeometry.Scheme.Modules

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let citations := Colib.Library.citations env
  let endpoints : List (Name × String) := [
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentUnit.lean:33-36"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_hom_terms,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentUnit.lean:59-76"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_inv_terms,
      "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentUnit.lean:79-95"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso,
      "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
        SectionUnitAction.lean:28-31"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom,
      "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
        SectionUnitNaturality.lean:31-46"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso_coefficient_hom,
      "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
        SectionUnitNaturality.lean:83-99"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectGlobalUnitIso,
      "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
        GlobalUnit.lean:25-28"),
    (``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectPullback_map_globalUnit,
      "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
        GlobalUnitPullback.lean:22-36"),
    (``AlgebraicGeometry.Scheme.Modules.pullback_map_globalSmulCenter,
      "Quillen/Aglib/AlgebraicGeometry/Modules/Scalar/Pullback.lean:22-54")]
  for (decl, locator) in endpoints do
    unless citations.any (fun c => c.declName == decl && c.source == "quillen" &&
        c.locator == locator && c.relation == "adaptation") do
      throwError "Missing precise compiled Quillen citation for {decl}"
  for decl in [``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso,
      ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom,
      ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso_coefficient_hom,
      ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso] do
    unless (Colib.Library.bindings env).any (fun b =>
        b.declName == decl && b.id == "COL-0359") do
      throwError "Missing compiled COL-0359 binding for {decl}"

open Lean Elab Command in
run_cmd do
  let declarations : List Name := [
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoefficientMap_T,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_evaluation,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_coefficient,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_iso,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_inv,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_hom_terms,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionLaurentUnitIso_inv_terms,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso,
    ``boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_hom,
    ``boundedAboveFlatAffineOriginalEvaluation_map_sectionUnitIso_inv,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineEvaluationAt_mapIso_sectionUnitIso,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_inv,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso_section_naturality,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso_coefficient_hom,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso_coefficient,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionUnitIso_coefficient_inv,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectGlobalUnitIso,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectGlobalUnitIso_hom_original,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectGlobalUnitIso_inv_original,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectGlobalUnitIso_hom_terms,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectGlobalUnitIso_inv_terms,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectPullback_map_globalUnit,
    ``AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectPullback_map_globalUnit_inv,
    ``AlgebraicGeometry.Scheme.Modules.globalSmulCenter_pushforward,
    ``AlgebraicGeometry.Scheme.Modules.pullback_map_globalSmulCenter,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoefficientMap,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate_val,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate_inv_val,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate_image,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate_image_inv,
    ``AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate_coefficient,
    ``CategoryTheory.Functor.IdentityAutomorphism.lift,
    ``CategoryTheory.Functor.IdentityAutomorphism.map_lift_hom,
    ``CategoryTheory.Functor.IdentityAutomorphism.map_lift_inv,
    ``CategoryTheory.Functor.IdentityAutomorphism.onFunctor,
    ``CategoryTheory.Functor.IdentityAutomorphism.onFunctor_hom_app,
    ``CategoryTheory.Functor.IdentityAutomorphism.mapIso_app_eq,
    ``CategoryTheory.Functor.IdentityAutomorphism.map_inv_app_eq,
    ``CategoryTheory.Functor.IdentityAutomorphism.whisker_hom_eq_of_evaluation]
  for decl in declarations do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
