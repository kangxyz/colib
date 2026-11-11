/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentialization
public import Colib.Topology.Prespectrum.HomotopyPushoutSeparation
public import Colib.Topology.Prespectrum.PushoutRightInclusionStable
public import Colib.Topology.Prespectrum.TelescopeHomotopyMapStable
public import Colib.Topology.Prespectrum.StableLocalization

/-!
# Genuine stable comparison with a canonical pushout sequentialization

The sequential stages are the original homotopy pushouts, not a tower of chosen inverses.
Positive-level point HEP passes through that recurrence. Stable unit legs and genuine
cone-to-fiber excision for the original attaching comparisons and right inclusions make
every original stage comparison stable. T1 original stages then give stability of the
actual whole-track telescope map and its isomorphism in the existing stable localization.

The factorization homotopies and row-excision premises remain explicit. This general
comparison does not identify a proposed action with Thomason--Trobaugh's tensor action.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)

/-- Original positive-level point HEP is preserved by the exact sequentialization recurrence. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationStable.lean:37"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem stage_point_homotopyExtensionProperty
    (hE : ∀ n k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((E n).point (k + 1)))))
    (hV : ∀ n k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((V n).point (k + 1)))))
    (n k : ℕ) : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((stage E V a b n).point (k + 1)))) := by
  induction n with
  | zero => exact hE 0 k
  | succ n ih =>
    cases n with
    | zero => exact hV 0 k
    | succ n =>
      exact HomotopyPushout.point_homotopyExtensionProperty
        (comparison E V a b (n + 1)) (a (n + 1)) (k + 1) (hE (n + 1) k) ih (hV (n + 1) k)

/-- T1 original vertices give T1 actual sequential stages. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationStable.lean:54"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem stageSpaceT1Space [∀ n k, T1Space ((E n).space k)]
    [∀ n k, T1Space ((V n).space k)] (n k : ℕ) : T1Space ((stage E V a b n).space k) := by
  induction n with
  | zero => exact inferInstanceAs (T1Space ((E 0).space k))
  | succ n ih =>
    cases n with
    | zero => exact inferInstanceAs (T1Space ((V 0).space k))
    | succ n =>
      let : T1Space ((stage E V a b (n + 1)).space k) := ih
      change T1Space ((HomotopyPushout.prespectrum
        (comparison E V a b (n + 1)) (a (n + 1))).space k)
      infer_instance

variable
    (hE : ∀ n k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((E n).point (k + 1)))))
    (hV : ∀ n k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((V n).point (k + 1)))))
    (hb : ∀ n, IsStableEquivalence (b n))
    (he : ∀ n, IsStableEquivalence
      (mappingConeFiberComparison (comparison E V a b (n + 1))))
    (hi : ∀ n, IsStableEquivalence (mappingConeFiberComparison
      (HomotopyPushout.inr (comparison E V a b (n + 1)) (a (n + 1)))))

include hE hV hb he hi in
/-- The original comparisons are stable by unit-leg stability and genuine row excision. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationStable.lean:80"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem comparison_isStableEquivalence (n : ℕ) :
    IsStableEquivalence (comparison E V a b n) := by
  cases n with
  | zero => exact IsStableEquivalence.id (E 0)
  | succ n =>
    induction n with
    | zero => exact hb 0
    | succ n ih =>
      change IsStableEquivalence (b (n + 1) ≫
        HomotopyPushout.inr (comparison E V a b (n + 1)) (a (n + 1)))
      exact (hb (n + 1)).comp
        (HomotopyPushout.inr_isStableEquivalence_of_excision
          (comparison E V a b (n + 1)) (a (n + 1)) (hE (n + 1))
          (fun k ↦ stage_point_homotopyExtensionProperty E V a b hE hV (n + 1) k)
          (hV (n + 1)) (he n) (hi n) ih)

variable (f : ∀ n, E n ⟶ E (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ b n))
    [∀ n k, T1Space ((E n).space k)] [∀ n k, T1Space ((V n).space k)]

include hE hV hb he hi in
/-- Actual stage maps and whole tracks give a stable equivalence of the original telescopes. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationStable.lean:102"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem telescopeMap_isStableEquivalence_of_excision :
    IsStableEquivalence (telescopeMap E V a b f H) := by
  let : ∀ n k, T1Space ((stage E V a b n).space k) := stageSpaceT1Space E V a b
  exact Telescope.mapOfHomotopies_isStableEquivalence E f
    (stage E V a b) (transition E V a b) (comparison E V a b)
    (comparisonTrack E V a b f H) (comparison_isStableEquivalence E V a b hE hV hb he hi)

/-- The resulting localization isomorphism is the image of that same actual telescope map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationStable.lean:110"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
def telescopeIso :
    toStableLocalization.obj (Telescope.prespectrum E f) ≅
      toStableLocalization.obj (Telescope.prespectrum (stage E V a b) (transition E V a b)) :=
  stableLocalizationIso (telescopeMap E V a b f H)
    (telescopeMap_isStableEquivalence_of_excision E V a b hE hV hb he hi f H)

end Topology.LoopPrespectrum.ZigzagSequentialization
