/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationDiagram
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialInitial

/-! Original current sources and actual initial legs of the supported tensor presentation. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
universe u
namespace ColibTest.ParameterTensorPresentation
open ModelZigzagSequentialization SchemeTrackSequentialPresentation

/-- The original supported initial inclusion reaches the actual first forward colimit leg. -/
theorem original_supported_initial {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) :
    Telescope.inclusion (vertex squareFunctor (ParameterModels.supported f) X)
        (current (ParameterModels.supported f) (ParameterLaurentTrack.supportedTrack f) X) 0 ≫
          ParameterTensorPresentation.supportedComparison f X =
      ZigzagSequentialization.initialColimitMap
        (vertex squareFunctor (ParameterModels.supported f) X)
        (suspendedVertex squareFunctor (ParameterModels.supported f) X)
        (forward (ParameterModels.supported f)
          (ParameterTensorNormalizedTrack.supportedTrack f) X)
        (unit squareFunctor (ParameterModels.supported f) X) :=
  comparisonOfEq_initial_leg _ _ _ _ _

/-- The comparison is stable at an arbitrary scheme parameter, including the integer base. -/
theorem original_supported_stable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterTensorPresentation.supportedComparison f X) :=
  ParameterTensorPresentation.supportedComparison_stable f X

/-- The chosen supported object is the actual ordinary colimit of the entire pushout sequence. -/
def originalSupportedColimit {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) :
    CategoryTheory.Limits.IsColimit (ZigzagSequentialization.ordinaryCocone
      (vertex squareFunctor (ParameterModels.supported f) X)
      (suspendedVertex squareFunctor (ParameterModels.supported f) X)
      (forward (ParameterModels.supported f)
        (ParameterTensorNormalizedTrack.supportedTrack f) X)
      (unit squareFunctor (ParameterModels.supported f) X)) :=
  ZigzagSequentialization.ordinaryIsColimit _ _ _ _

end ColibTest.ParameterTensorPresentation

open AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ambientComparison Q X) := ambientComparison_stable Q X
example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (supportedComparison f X) := supportedComparison_stable f X
example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope (ParameterLaurentTrack.ambientTrack Q)).obj X ⟶
      ambient Q X := ambientComparison Q X
