/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientFineTelescopeComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageInclusionComparison

/-!
# Original finite-stage classes in the current parameter telescope

The actual integral Spec-row isomorphism and original section restriction
transport the proved fine inclusion range to the original iterated parameter
tower. The genuine finite-stage and telescope comparisons then give the same
range for the independent current-stage inclusion. No conjugating word is
identified with an identity, and no class map is defined by a telescope inverse.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex SchemeNaturalSeed GlobalSupportedSection
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- The literal inclusion into the original iterated-seed parameter telescope. -/
def iteratedStageInclusion (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram P) ⟶ parameterTelescope P.left :=
  Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj
    (parameterDiagram P))
    (strictDiagramTransition squareFunctor (seed (ParameterLaurentTrack.ambientTrack P.left))) i

/-- The literal inclusion into the independently defined current-stage parameter telescope. -/
def currentStageInclusion (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram P) ⟶
      currentTelescope (ParameterLaurentTrack.ambientTrack P.left) :=
  Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj
    (parameterDiagram P)) (currentTransition (ParameterLaurentTrack.ambientTrack P.left)) i

/-- The actual Spec comparison keeps the original stage inclusion at its original height zero. -/
theorem iteratedStageInclusion_telescopeIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (iteratedStageInclusion P i).app (specUnder.obj a) ≫ (telescopeIso P).hom.app a =
      (finiteIso P i).hom.app a ≫
        (Telescope.diagramInclusion (globalDiagram P) (globalTransition P) i).app a := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

variable [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- Original global stage inclusions have the exact fine stable range. -/
theorem globalStageInclusion_isIso_of_le (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion (globalDiagram P) (globalTransition P) i).app a)) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map ((telescopeRestriction P).app a)) :=
    telescopeRestriction_isStableEquivalence P a d
  let : IsIso (H.map ((finiteRestriction P i).app a)) :=
    finiteRestriction_isStableEquivalence P i a d
  let : IsIso (H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i).app a)) :=
    boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_isIso_of_le P i a d hd
  have h := congrArg H.map (congrArg (fun η => η.app a)
    (telescopeRestriction_inclusion P i))
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((telescopeRestriction P).app a)), h]
  infer_instance

/-- The actual iterated parameter inclusion is invertible in every original finite-stage range. -/
theorem iteratedStageInclusion_isIso_of_le (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((iteratedStageInclusion P i).app (specUnder.obj a))) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map
      ((Telescope.diagramInclusion (globalDiagram P) (globalTransition P) i).app a)) :=
    globalStageInclusion_isIso_of_le P i a d hd
  have h := congrArg H.map (iteratedStageInclusion_telescopeIso P i a)
  simp only [Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((telescopeIso P).hom.app a)), h]
  infer_instance

/-- The independent current inclusion is invertible in the same range without erasing its word. -/
theorem currentStageInclusion_isIso_of_le (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((currentStageInclusion P i).app (specUnder.obj a))) :=
  (model_currentInclusion_isIso_iff_iteratedInclusion (ParameterModels.ambient P.left)
    (ParameterLaurentTrack.ambientTrack P.left) i (specUnder.obj a) d).mpr
      (iteratedStageInclusion_isIso_of_le P i a d hd)

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
