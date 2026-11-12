/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentation
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialComparisonStable

/-! Actual scheme diagrams and original-current natural comparisons for the tensor presentation. -/
/-!
Implementation provenance: adapted from Quillen at
`ParameterTensorPresentationDiagram.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex SchemeNaturalSeed

/-- The genuine ambient ordinary-colimit objects with their original scheme input maps. -/
def ambientDiagram (Q : Scheme.{u}) : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1} :=
  SchemeTrackSequentialPresentation.diagram (ParameterModels.ambient Q)
    (ParameterTensorNormalizedTrack.ambientTrack Q)

/-- Whole scheme naturality of the comparison from the literal original ambient current tower. -/
def ambientComparisonNatTrans (Q : Scheme.{u}) :
    currentTelescope (ParameterLaurentTrack.ambientTrack Q) ⟶ ambientDiagram Q :=
  SchemeTrackSequentialPresentation.comparisonNatTransOfEq (ParameterModels.ambient Q)
    (ParameterLaurentTrack.ambientTrack Q) (ParameterTensorNormalizedTrack.ambientTrack Q)
    (ParameterTensorNormalizedTrack.ambientTrack_eq Q).symm

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The genuine supported ordinary-colimit objects with their original scheme input maps. -/
def supportedDiagram : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1} :=
  SchemeTrackSequentialPresentation.diagram (ParameterModels.supported f)
    (ParameterTensorNormalizedTrack.supportedTrack f)

/-- Whole scheme naturality of the comparison from the literal original supported current tower. -/
def supportedComparisonNatTrans :
    currentTelescope (ParameterLaurentTrack.supportedTrack f) ⟶ supportedDiagram f :=
  SchemeTrackSequentialPresentation.comparisonNatTransOfEq (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedTrack f) (ParameterTensorNormalizedTrack.supportedTrack f)
    (ParameterTensorNormalizedTrack.supportedTrack_eq f).symm

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
