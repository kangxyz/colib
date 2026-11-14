/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageZeroComparison

/-! # Isomorphism detection for every original current-stage inclusion

The actual finite stage maps and three telescope maps compare the current and
iterated-seed inclusions through the normalized and twisted telescopes. The
conjugating word remains its genuine isomorphism at every stage; it is not
replaced by an identity. All signed stable degrees are retained.

Source: `Quillen/KTheory/Bass/SchemeStageInclusionComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
  (i : ℕ) (X : Scheme.{u}ᵒᵖ) (d : ℤ)

/-- The literal current inclusion is invertible exactly when the normalized inclusion is. -/
theorem model_currentInclusion_isIso_iff_normalizedInclusion :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion
        (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
        (currentTransition A) i).app X)) ↔
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion (fun j => normalized squareFunctor j (M ⋙ prespectrumFunctor))
        (normalizedTransition A) i).app X)) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map ((telescopeMap A).app X)) := model_telescopeMap_stable M A X d
  let : IsIso (H.map ((stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X)) :=
    model_stageMap_stable squareFunctor i M X d
  have h := congrArg H.map (congrArg (fun η => η.app X) (telescopeMap_inclusion A i))
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((telescopeMap A).app X)), h,
    isIso_comp_left_iff]

/-- The literal normalized inclusion is invertible exactly when the twisted inclusion is. -/
theorem model_normalizedInclusion_isIso_iff_twistedInclusion :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion (fun j => normalized squareFunctor j (M ⋙ prespectrumFunctor))
        (normalizedTransition A) i).app X)) ↔
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion (fun j => normalized squareFunctor j (M ⋙ prespectrumFunctor))
        (twistedTransition A) i).app X)) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map ((conjugacyTelescopeMap A).app X)) :=
    model_conjugacyTelescopeMap_stable M A X d
  let : IsIso (H.map ((conjugatingIso i (M ⋙ prespectrumFunctor)).hom.app X)) :=
    by infer_instance
  have h := congrArg H.map (congrArg (fun η => η.app X) (conjugacyTelescopeMap_inclusion A i))
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((conjugacyTelescopeMap A).app X)), h,
    isIso_comp_left_iff]

/-- The literal iterated inclusion is invertible exactly when the twisted inclusion is. -/
theorem model_iteratedInclusion_isIso_iff_twistedInclusion :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion
        (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
        (strictDiagramTransition squareFunctor (seed A)) i).app X)) ↔
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion (fun j => normalized squareFunctor j (M ⋙ prespectrumFunctor))
        (twistedTransition A) i).app X)) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap A).app X)) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable M A X d
  let : IsIso (H.map ((stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X)) :=
    model_stageMap_stable squareFunctor i M X d
  have h := congrArg H.map (congrArg (fun η => η.app X)
    (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap_inclusion A i))
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [← isIso_comp_right_iff _
    (H.map ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap A).app X)), h,
    isIso_comp_left_iff]

/-- All signed degrees detect the same inclusion isomorphisms in the two original towers. -/
theorem model_currentInclusion_isIso_iff_iteratedInclusion :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion
        (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
        (currentTransition A) i).app X)) ↔
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion
        (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
        (strictDiagramTransition squareFunctor (seed A)) i).app X)) :=
  (model_currentInclusion_isIso_iff_normalizedInclusion M A i X d).trans
    ((model_normalizedInclusion_isIso_iff_twistedInclusion M A i X d).trans
      (model_iteratedInclusion_isIso_iff_twistedInclusion M A i X d).symm)

end KTheory.Bass.SchemeNaturalSeed
