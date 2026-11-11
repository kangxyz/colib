/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedTransition
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedInputNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.Topology.Prespectrum.TelescopeStableEquivalence

/-! # The original iterated-seed to twisted-normalized telescope comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum.FiniteParameterLooping
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTelescope
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open SchemeNaturalSeed SchemeIteratedSeedTransition
open FiniteConeTopology
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The existing finite stage maps descend to a natural map
of the original and twisted telescopes. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedTelescope.lean:32"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
def iteratedTwistedTelescopeMap (A : Track laurent.op coefficient F) :
    iteratedTelescope A ⟶ twistedTelescope A :=
  Telescope.diagramMap (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (fun i => normalized squareFunctor i F)
    (strictDiagramTransition squareFunctor (seed A)) (twistedTransition A)
    (fun i => stageMap squareFunctor i F) (fun i => (originalTransition_stageMap A i).symm)

/-- Every original telescope cylinder keeps its stage and entire height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedTelescope.lean:40"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem iteratedTwistedTelescopeMap_cylinder (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((iteratedTwistedTelescopeMap A).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed A) j).app X) n i (s, x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
      (fun j => (twistedTransition A j).app X) n i
      (s, ((stageMap squareFunctor i F).app X).map n x) :=
  Telescope.diagramMap_cylinder
    (fun j => (strictDiagramIterate squareFunctor j).obj F)
    (fun j => normalized squareFunctor j F)
    (strictDiagramTransition squareFunctor (seed A)) (twistedTransition A)
    (fun j => stageMap squareFunctor j F)
    (fun j => (originalTransition_stageMap A j).symm) X n i s x

/-- Original finite-stage inclusions commute with the same telescope map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedTelescope.lean:57"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem iteratedTwistedTelescopeMap_inclusion (A : Track laurent.op coefficient F) (i : ℕ) :
    Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj F)
        (strictDiagramTransition squareFunctor (seed A)) i ≫ iteratedTwistedTelescopeMap A =
      stageMap squareFunctor i F ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
          (twistedTransition A) i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- Genuine Model input makes this same iterated-seed telescope map stable on every scheme. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedTelescope.lean:66"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem model_iteratedTwistedTelescopeMap_stable
    (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((iteratedTwistedTelescopeMap A).app X) := by
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
    (fun i => (strictDiagramTransition squareFunctor (seed A) i).app X)
    (fun i => (normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X)
    (fun i => (twistedTransition A i).app X)
    (fun i => (stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X)
    (fun i => congrArg (fun η => η.app X) (originalTransition_stageMap A i).symm)
    (fun i => model_stageMap_stable squareFunctor i M X)

end KTheory.Bass.SchemeIteratedSeedTelescope

namespace KTheory.Bass.SchemeIteratedSeedTelescope

attribute [colib_tag "COL-0584"] model_iteratedTwistedTelescopeMap_stable

end KTheory.Bass.SchemeIteratedSeedTelescope
