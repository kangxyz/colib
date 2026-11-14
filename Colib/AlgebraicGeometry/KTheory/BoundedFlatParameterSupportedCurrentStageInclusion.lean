/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescope

/-!
# The actual finite inclusions into the supported parameter telescopes

These inclusions preserve the original height-zero representatives under the integral
Spec-row comparison. No invertibility range is asserted here.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
  ParameterSupportedCurrentStageInclusion.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSectionChangeIndex.SupportedTelescope SchemeNaturalSeed
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The literal inclusion into the original iterated-seed parameter telescope. -/
def iteratedStageInclusion (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram f) ⟶ parameterTelescope f.left :=
  Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj
    (parameterDiagram f))
    (strictDiagramTransition squareFunctor (seed (ParameterLaurentTrack.supportedTrack f.left))) i

/-- The literal inclusion into the independently defined current-stage parameter telescope. -/
def currentStageInclusion (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram f) ⟶
      currentTelescope (ParameterLaurentTrack.supportedTrack f.left) :=
  Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj
    (parameterDiagram f)) (currentTransition (ParameterLaurentTrack.supportedTrack f.left)) i

/-- The actual Spec comparison keeps the original stage inclusion at its original height zero. -/
theorem iteratedStageInclusion_telescopeIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (iteratedStageInclusion f i).app (specUnder.obj a) ≫ (telescopeIso f).hom.app a =
      (finiteIso f i).hom.app a ≫
        (Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i).app a := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
