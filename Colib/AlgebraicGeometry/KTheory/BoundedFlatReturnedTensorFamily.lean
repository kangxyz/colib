/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.ConeGeneratorRecognition
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedStrictification
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedCell

/-! Actual returned tensor data instantiate the generator recognition criterion. -/
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
open GlobalSupportedSection
open AlgebraicGeometry.RingedSpace

/-- The input is actual returned tensor multiplication, with its proved evaluation conjugation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorFamily.lean:26-30"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
def tensorFamily (Q : Scheme.{u}) :=
  ModelUnitRowStrictification.family laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q)

/-- The tensor cell's four-arrow compatibility is proved, not a new hypothesis of recognition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorFamily.lean:33-42"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
theorem tensorFamily_naturality (Q : Scheme.{u})
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterModels.ambient Q).obj X)).space n) :
    ((DiagramRowRefinement.diagram (ParameterModels.ambient Q ⋙ prespectrumFunctor)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q))).map (laurent.op.map g)).map n
        (((tensorFamily Q).val X).level n (r, x)) =
      ((tensorFamily Q).val Y).level n
        (r, (prespectrumMap ((ParameterModels.ambient Q).map g)).map n x) :=
  (tensorFamily Q).property.1 g n r x


end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

attribute [colib_tag "COL-0557"] tensorFamily_naturality

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
