/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionPiZeroNaturality

/-! Native axiom closure and compiled Library bindings for every public production declaration. -/

open Lean Elab Command in
run_cmd do
  let declarations : List Name := [
    ``CategoryTheory.GroupCompletion.Localization.Components,
    ``CategoryTheory.GroupCompletion.Localization.componentClass,
    ``CategoryTheory.GroupCompletion.Localization.componentClass_hom,
    ``CategoryTheory.GroupCompletion.Localization.componentClass_iso,
    ``CategoryTheory.GroupCompletion.Localization.componentClass_eq_iff,
    ``CategoryTheory.GroupCompletion.Localization.componentsZero,
    ``CategoryTheory.GroupCompletion.Localization.componentsAdd,
    ``CategoryTheory.GroupCompletion.Localization.componentClass_tensor,
    ``CategoryTheory.GroupCompletion.Localization.componentClass_unit,
    ``CategoryTheory.GroupCompletion.Localization.componentsAddCommMonoid,
    ``CategoryTheory.GroupCompletion.Localization.componentsNeg,
    ``CategoryTheory.GroupCompletion.Localization.componentClass_switch,
    ``CategoryTheory.GroupCompletion.Localization.components_neg_add_cancel,
    ``CategoryTheory.GroupCompletion.Localization.componentsAddCommGroup,
    ``CategoryTheory.GroupCompletion.Localization.componentUnitClass,
    ``CategoryTheory.GroupCompletion.Localization.componentUnitClass_unit,
    ``CategoryTheory.GroupCompletion.Localization.componentUnitClass_tensor,
    ``CategoryTheory.GroupCompletion.Localization.componentUnitClass_iso,
    ``CategoryTheory.GroupCompletion.Localization.componentDenominatorArrow,
    ``CategoryTheory.GroupCompletion.Localization.componentClass_pair_eq_sub,
    ``CategoryTheory.GroupCompletion.monoidalMapComponents,
    ``CategoryTheory.GroupCompletion.monoidalMapComponents_apply,
    ``CategoryTheory.GroupCompletion.monoidalMapComponents_unitClass,
    ``CategoryTheory.GroupCompletion.Localization.swapLinear,
    ``CategoryTheory.GroupCompletion.Localization.switch,
    ``CategoryTheory.GroupCompletion.Localization.switch_obj,
    ``CategoryTheory.GroupCompletion.Localization.switch_mkHom,
    ``CategoryTheory.GroupCompletion.Localization.switch_map_switch,
    ``CategoryTheory.GroupCompletion.Localization.switch_comp_switch,
    ``CategoryTheory.GroupCompletion.Localization.switchEquivalence,
    ``CategoryTheory.GroupCompletion.Localization.braidingIso,
    ``CategoryTheory.GroupCompletion.Localization.braidingIso_naturality,
    ``CategoryTheory.GroupCompletion.Localization.braidedCategory,
    ``CategoryTheory.GroupCompletion.Localization.symmetricCategory,
    ``ModuleCat.FiniteProjective.completionComponentsAddCommGroup,
    ``ModuleCat.FiniteProjective.completionComponentGrade,
    ``ModuleCat.FiniteProjective.completionComponentGrade_mk,
    ``ModuleCat.FiniteProjective.componentUnitClass_additive,
    ``ModuleCat.FiniteProjective.grothendieckToCompletionComponents,
    ``ModuleCat.FiniteProjective.grothendieckToCompletionComponents_class,
    ``ModuleCat.FiniteProjective.completionComponentGrade_comp_grothendieckToCompletionComponents,
    ``ModuleCat.FiniteProjective.grothendieckToCompletionComponents_comp_completionComponentGrade,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_pair,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_symm_class,
    ``ModuleCat.FiniteProjective.completionGrade_eq_iff_zigzag,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_mk,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_pair,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_symm_class,
    ``ModuleCat.FiniteProjective.completion_joined_iff_grade_eq,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_baseChange,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_baseChange_hom,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_baseChange,
    ``CategoryTheory.classifyingSpaceVertexComponents,
    ``CategoryTheory.classifyingSpaceComponentToZerothHomotopy,
    ``CategoryTheory.classifyingSpaceComponentIndex,
    ``CategoryTheory.classifyingSpaceComponentIndex_point,
    ``CategoryTheory.classifyingSpaceComponentIndex_eq_of_joined,
    ``CategoryTheory.classifyingSpaceComponentsEquiv,
    ``CategoryTheory.classifyingSpaceComponentsEquiv_mk,
    ``CategoryTheory.classifyingSpaceComponentsEquiv_symm_mk,
    ``CategoryTheory.classifyingSpaceComponentsEquiv_naturality]
  for decl in declarations do
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"Checked allowed axiom closure of {declarations.length} production declarations"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let endpoints : List Name := [
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_pair,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_symm_class,
    ``ModuleCat.FiniteProjective.completionGrade_eq_iff_zigzag,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_pair,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_symm_class,
    ``ModuleCat.FiniteProjective.completion_joined_iff_grade_eq,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_baseChange,
    ``ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_baseChange_hom,
    ``ModuleCat.FiniteProjective.completionPiZeroGrothendieckEquiv_baseChange]
  for decl in endpoints do
    unless (Colib.Library.bindings env).any
        (fun b => b.declName == decl && b.id == "COL-0378") do
      throwError "Missing compiled COL-0378 binding for {decl}"
    unless (Colib.Library.citations env).any
        (fun c => c.declName == decl && c.source == "WeibelKBook" &&
          c.locator.startsWith "IV,") do
      throwError "Missing precise comparison citation for {decl}"
  logInfo m!"Checked {endpoints.length} compiled COL-0378 bindings and references"
