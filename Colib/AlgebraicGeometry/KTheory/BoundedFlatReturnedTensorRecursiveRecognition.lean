/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGenerators

/-! Concrete tensor-rooted recursive cone recognition, with the original index and row maps. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
open GlobalSectionChangeIndex ModelDiagramRowInterchange ParameterTensorEvaluationRow
open GlobalSupportedSection GeometricSquareInterchange

/-- The existing finite recursion is rooted in the actual returned tensor family, not supplied
comparison data or a family chosen separately at later stages. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:24-35"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
def tensorStageFamily (Q : Scheme.{u}) (i : ℕ) :=
  DiagramRowCell.iterateFamily laurent.op coefficient squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i (ParameterModels.ambient Q ⋙ prespectrumFunctor)
    (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
    (initial_naturality (ParameterModels.ambient Q))
    (initial_structure (ParameterModels.ambient Q))
    (NaturalTrack.ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
      (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q))
    (tensorFamily Q)

/-- This is literally the previously constructed tensor-started cell. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:38-39"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensorStageFamily_cell (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (tensorStageFamily Q i).val X = strictifiedIteratedCell Q i X := rfl

/-- At each actual finite stage, take its four tensor-rooted corner cells. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:42-44"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
def tensorStageSquare (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  diagramSquareMapHomotopy (tensorStageFamily Q i).val
    (tensorStageFamily Q i).property.1 (squareFunctor.obj X)

/-- The original geometric index inverse and forward row strength, before old-loop conversion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:47-60"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
def tensorStageTransport (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (ConeTrack.indexMap squareFunctor laurent.op
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (DiagramRowRefinement.diagram
      ((strictDiagramIterate squareFunctor i).obj (ParameterModels.ambient Q ⋙ prespectrumFunctor))
      (stage squareFunctor (ParameterModels.ambient Q) i)
      (stage_point squareFunctor (ParameterModels.ambient Q) i)
      (stage_naturality squareFunctor (ParameterModels.ambient Q) i))).app X ≫
    DiagramConeRowStrength.strength squareFunctor
      ((strictDiagramIterate squareFunctor i).obj (ParameterModels.ambient Q ⋙ prespectrumFunctor))
      (stage squareFunctor (ParameterModels.ambient Q) i)
      (stage_point squareFunctor (ParameterModels.ambient Q) i)
      (stage_naturality squareFunctor (ParameterModels.ambient Q) i) (laurent.op.obj X)

/-- The old-loop/row conversion is the computed map, including its degree-zero coordinates. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:63-69"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
def tensorStageLoopRowInverse (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  DiagramRowCell.loopRowInverse
    ((strictDiagramIterate squareFunctor i).obj (ParameterModels.ambient Q ⋙ prespectrumFunctor))
    (stage squareFunctor (ParameterModels.ambient Q) i)
    (stage_point squareFunctor (ParameterModels.ambient Q) i)
    (stage_naturality squareFunctor (ParameterModels.ambient Q) i)
    squareFunctor (laurent.op.obj X)

/-- The existing raw successor constructor applied to the actual tensor-rooted stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:72-81"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
def tensorStageRawBass (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  DiagramRowCell.rawBass laurent.op coefficient
    ((strictDiagramIterate squareFunctor i).obj (ParameterModels.ambient Q ⋙ prespectrumFunctor))
    (stage squareFunctor (ParameterModels.ambient Q) i)
    (stage_point squareFunctor (ParameterModels.ambient Q) i)
    (stage_naturality squareFunctor (ParameterModels.ambient Q) i)
    (stage_structure squareFunctor (ParameterModels.ambient Q) i)
    (tensorStageFamily Q i).val (tensorStageFamily Q i).property.1 squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) X

/-- The inherited cone action is characterized by the actual four corner generators. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:84-87"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensorStage_generators (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    StrictSquare.MapHomotopy.ConeGeneratorLaw (tensorStageSquare Q i X)
      (tensorStageSquare Q i X).cone :=
  StrictSquare.MapHomotopy.cone_generatorLaw _

/-- Any inherited cone action with those generator values gives the very same successor cell
through the original index transport, row strength, and loop/row conversion. No all-stage
comparison is an input to this uniqueness assertion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorRecursiveRecognition.lean:92-99"
  "adaptation" "Original tensor-rooted finite recursion and independent coordinate formulas."]
theorem tensorStage_successor_unique (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy _ _)
    (h : StrictSquare.MapHomotopy.ConeGeneratorLaw (tensorStageSquare Q i X) K) :
    ((K.postcomp (tensorStageTransport Q i X)).parameterLooping).postcomp
        (tensorStageLoopRowInverse Q i X) =
      tensorStageRawBass Q i X := by
  rw [StrictSquare.MapHomotopy.eq_cone_of_generatorLaw _ K h]
  rfl

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

attribute [colib_tag "COL-0558"] tensorStage_successor_unique

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
