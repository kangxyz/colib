/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorNormalizedTrack
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialTransport
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescope

/-!
# Actual ordinary-colimit tensor presentations on the localization parameter Models

Ambient and supported objects use their original Model diagrams and actual tensor-normalized
units. The source comparisons are precisely the original current telescopes, using the proved
whole track equalities. The full-open endpoint uses the ambient construction on the open scheme.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex GlobalSupportedSection SchemeNaturalSeed

/-- The actual ordinary pushout colimit for the original ambient parameter Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorPresentation.lean:28"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def ambient (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  SchemeTrackSequentialPresentation.presentation (ParameterModels.ambient Q)
    (ParameterTensorNormalizedTrack.ambientTrack Q) X

/-- The exact original current ambient telescope maps to the genuine normalized presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorPresentation.lean:33"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def ambientComparison (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (currentTelescope (ParameterLaurentTrack.ambientTrack Q)).obj X ⟶ ambient Q X :=
  SchemeTrackSequentialPresentation.comparisonOfEq (ParameterModels.ambient Q)
    (ParameterLaurentTrack.ambientTrack Q) (ParameterTensorNormalizedTrack.ambientTrack Q)
    (ParameterTensorNormalizedTrack.ambientTrack_eq Q).symm X

/-- The actual ambient comparison is stable without additional localization assumptions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorPresentation.lean:40"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem ambientComparison_stable (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ambientComparison Q X) :=
  SchemeTrackSequentialPresentation.comparisonOfEq_stable (ParameterModels.ambient Q)
    (ParameterLaurentTrack.ambientTrack Q) (ParameterTensorNormalizedTrack.ambientTrack Q)
    (ParameterTensorNormalizedTrack.ambientTrack_eq Q).symm X

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The supported presentation uses the original support full subcategory at every parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorPresentation.lean:49"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def supported (X : Scheme.{u}ᵒᵖ) :=
  SchemeTrackSequentialPresentation.presentation (ParameterModels.supported f)
    (ParameterTensorNormalizedTrack.supportedTrack f) X

/-- The exact original supported current telescope maps to the actual supported colimit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorPresentation.lean:54"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def supportedComparison (X : Scheme.{u}ᵒᵖ) :
    (currentTelescope (ParameterLaurentTrack.supportedTrack f)).obj X ⟶ supported f X :=
  SchemeTrackSequentialPresentation.comparisonOfEq (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedTrack f) (ParameterTensorNormalizedTrack.supportedTrack f)
    (ParameterTensorNormalizedTrack.supportedTrack_eq f).symm X

/-- Stability uses only actual finite Model topology and the proved whole track identity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorPresentation.lean:61"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem supportedComparison_stable (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (supportedComparison f X) :=
  SchemeTrackSequentialPresentation.comparisonOfEq_stable (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedTrack f) (ParameterTensorNormalizedTrack.supportedTrack f)
    (ParameterTensorNormalizedTrack.supportedTrack_eq f).symm X

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
