/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitFirstNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitRoutes
public import Colib.KTheory.Waldhausen.Iterated.CompositionHomotopyNaturality
public import Colib.Topology.Prespectrum.RelativeLevelEvaluation

/-! The original second split-unit comparisons and their mixed normalized route,
with the literal unit whiskerings at every level. Adapted from `OriginalUnitSquareSimplex.lean`
at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "idFirst" => BoundedFlatPerfectIdentitySimplex.first
local notation "idComparisonLevel" => BoundedFlatPerfectIdentitySimplex.identity_comparison_level
local notation "idMid" => BoundedFlatPerfectIdentitySimplex.intermediate
local notation "idSecond" => BoundedFlatPerfectIdentitySimplex.second
local notation "idSource" => BoundedFlatPerfectIdentitySimplex.source
local notation "idTarget" => BoundedFlatPerfectIdentitySimplex.target

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The right second triangle is the original target identity track precomposed by pullback. -/
theorem rightSecond_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightSecondParameter (r, t), x) =
      (Homotopy.RelHomotopy.precomp (K f)
        (boundedAboveFlatPerfectNormalizedIdTrackComparison X)).level n (r, (t, x)) := by
  refine (rightSecondParameter_lift f n r t x).trans ?_
  have h := prespectrumTransformationCompositionHomotopy_precomp_level
    (F := idSource X) (G := idMid X) (H := idTarget X)
    (idFirst X).hom (idSecond X).hom
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) (sourceMap f) n r t x
  exact h.trans ((DFunLike.congr_fun (idComparisonLevel X n)
    (r, (t, (K f).map n x))).symm)

/-- The left second triangle is the original source identity track postcomposed by pullback. -/
theorem leftSecond_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftSecondParameter (r, t), x) =
      ((boundedAboveFlatPerfectNormalizedIdTrackComparison Y).postcomp (K f)).level n
        (r, (t, x)) := by
  refine (leftSecondParameter_lift f n r t x).trans ?_
  have h := prespectrumTransformationCompositionHomotopy_postcomp_level
    (F := idSource Y) (G := idMid Y) (H := idTarget Y)
    (idFirst Y).hom (idSecond Y).hom
    (fun _ ↦ (W Y).asSmall.weq_iso _ inferInstance)
    (fun _ ↦ (W Y).asSmall.weq_iso _ inferInstance) (sourceMap f) n r t x
  exact h.trans (congrArg ((K f).map n)
    ((DFunLike.congr_fun (idComparisonLevel Y n) (r, (t, x))).symm))

/-- The normalized middle is the original two-triangle pasting, without changing its clock. -/
theorem normalized_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n
      ((normalizedRightParameter.symm.trans normalizedLeftParameter) (r, t), x) =
      (boundedAboveFlatPerfectNormalizedUnitRoutesComparison f).level n (r, (t, x)) := by
  unfold boundedAboveFlatPerfectNormalizedUnitRoutesComparison
  dsimp only
  rw [Homotopy.RelHomotopy.ofLevels_apply,
    originalPrespectrumPastingHomotopy_whole_level, Path.Homotopy.trans_apply]
  split
  · exact normalizedRightParameter_lift f n _ t x
  · exact normalizedLeftParameter_lift f n _ t x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex
