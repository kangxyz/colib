/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCell
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowPresentation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorInitialCell
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedInitialCell

/-!
# Tensor-qualified ambient and supported proper-row presentations

These presentations use the actual parameter Models and original Laurent
units whose initial cells have the genuine tensor/evaluation prism comparison.
All later forward legs are independently constructed by cone and loop
iteration, then joined to the original whole null. The resulting pointwise
stable comparisons do not by themselves assemble the classical auxiliary
fiber diagram or identify its original signed negative classes.
-/
@[expose] public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open Topology
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorRowPresentation
open GlobalSectionChangeIndex

/-- The actual ambient independent-cell proper-row presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:33"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def ambient (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{u + 1} :=
  SchemeModelRowSeed.presentation (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X

/-- The initial ambient cell is the same cell carrying the genuine tensor/evaluation prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:38"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem ambient_initialCell_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    SchemeModelRowSeed.cell (ParameterModels.ambient Q)
      (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) 0 X =
      ParameterTensorEvaluationRow.initialCell Q X := rfl

/-- The original ambient current telescope maps to that independently formed presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:44"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def ambientComparison (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope (ParameterLaurentTrack.ambientTrack Q)).obj X ⟶
      ambient Q X :=
  SchemeModelRowSeed.comparison (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X

/-- Original finite Model growth proves the ambient comparison stable in every integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:51"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem ambientComparison_stable (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ambientComparison Q X) :=
  SchemeModelRowSeed.comparison_stable (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) X

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual supported independent-cell presentation uses the supported unit itself. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:59"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def supported (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{u + 1} :=
  SchemeModelRowSeed.presentation (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f) X

/-- The initial supported cell is the original cell with its own supported tensor prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:64"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem supported_initialCell_eq (X : Scheme.{u}ᵒᵖ) :
    SchemeModelRowSeed.cell (ParameterModels.supported f)
      (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
      0 X = ParameterTensorSupportedRow.initialCell f X := rfl

/-- The original supported current telescope maps to the genuine supported row presentation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:70"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def supportedComparison (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope (ParameterLaurentTrack.supportedTrack f)).obj X ⟶
      supported f X :=
  SchemeModelRowSeed.comparison (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f) X

/-- Supported comparison stability uses its own actual Model topology. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean:77"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem supportedComparison_stable (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (supportedComparison f X) :=
  SchemeModelRowSeed.comparison_stable (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f) X

end AlgebraicGeometry.Scheme.Modules.ParameterTensorRowPresentation
