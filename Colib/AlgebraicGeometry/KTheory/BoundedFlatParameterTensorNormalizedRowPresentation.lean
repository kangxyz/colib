/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedPresentation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorInitialCell
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedInitialCell

/-!
# Ambient and supported normalized-boundary row presentations

The canonical zigzags use the independently normalized cell followed by the
original cone boundary. The original current telescope maps stably to each
presentation using the entire normalization homotopy. The actual tensor/cup
qualification and whole auxiliary-null compatibility are separate consumers.
-/
@[expose] public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open Topology
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedRowPresentation
open GlobalSectionChangeIndex

/-- The actual ambient independent-cell proper-row presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:31"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def ambient (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{u + 1} :=
  SchemeModelRowSeed.normalizedPresentation (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X

/-- The initial ambient cell is the same cell carrying the genuine tensor/evaluation prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:36"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem ambient_initialCell_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    SchemeModelRowSeed.cell (ParameterModels.ambient Q)
      (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) 0 X =
      ParameterTensorEvaluationRow.initialCell Q X := rfl

/-- The original ambient current telescope maps to that independently formed presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:42"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def ambientComparison (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope (ParameterLaurentTrack.ambientTrack Q)).obj X ⟶
      ambient Q X :=
  SchemeModelRowSeed.normalizedComparison (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X

/-- Original finite Model growth proves the ambient comparison stable in every integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:49"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem ambientComparison_stable (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ambientComparison Q X) :=
  SchemeModelRowSeed.normalizedComparison_stable (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual supported independent-cell presentation uses the supported unit itself. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:57"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def supported (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{u + 1} :=
  SchemeModelRowSeed.normalizedPresentation (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f) X

/-- The initial supported cell is the original cell with its own supported tensor prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:62"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem supported_initialCell_eq (X : Scheme.{u}ᵒᵖ) :
    SchemeModelRowSeed.cell (ParameterModels.supported f)
      (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
      0 X = ParameterTensorSupportedRow.initialCell f X := rfl

/-- The original supported current telescope maps to the genuine supported row presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:68"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def supportedComparison (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope (ParameterLaurentTrack.supportedTrack f)).obj X ⟶
      supported f X :=
  SchemeModelRowSeed.normalizedComparison (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f) X

/-- Supported comparison stability uses its own actual Model topology. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorNormalizedRowPres\
    entation.lean:75"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem supportedComparison_stable (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (supportedComparison f X) :=
  SchemeModelRowSeed.normalizedComparison_stable (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f) X

end AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedRowPresentation
