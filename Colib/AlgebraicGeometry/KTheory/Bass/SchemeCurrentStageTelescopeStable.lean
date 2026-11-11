/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescope
public import Colib.KTheory.Bass.NormalizedStageMapStable
public import Colib.KTheory.Bass.FiniteConeLoopTopology
public import Colib.KTheory.Bass.ModelDiagramConnectivity
public import Colib.Topology.Prespectrum.TelescopeStableEquivalence

/-! # Stability of the actual current-stage telescope map

Genuine finite Model topology and the original stage-map stability prove stability of the
same whole current-to-normalized telescope map. No additional stable premise is introduced.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap FiniteConeTopology

/-- Genuine Model input makes this same current-stage telescope map stable on every scheme. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageTelescope.lean:71"
  "adaptation" "Original actual current-to-normalized telescope stable comparison."]
theorem model_telescopeMap_stable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((telescopeMap A).app X) := by
  let : ∀ i n, T1Space
      ((((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space squareFunctor i M X n
  let : ∀ i n, T1Space
      ((normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X |>.space n) := by
    intro i n
    rw [normalized_obj]
    exact modelLoopsIterateSpaceT1Space squareFunctor i i M X n
  exact Telescope.map_isStableEquivalence
    (fun i => ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X)
    (fun i => (currentTransition A i).app X)
    (fun i => (normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X)
    (fun i => (normalizedTransition A i).app X)
    (fun i => (stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X)
    (fun i => congrArg (fun η => η.app X) (currentTransition_stageMap A i).symm)
    (fun i => model_stageMap_stable squareFunctor i M X)

end KTheory.Bass.SchemeNaturalSeed

namespace KTheory.Bass.SchemeNaturalSeed

attribute [colib_tag "COL-0566"] model_telescopeMap_stable

end KTheory.Bass.SchemeNaturalSeed
