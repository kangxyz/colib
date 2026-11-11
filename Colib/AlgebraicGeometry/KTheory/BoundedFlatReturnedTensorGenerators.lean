/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorFamily
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedStrictification
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientKOne
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

/-- The strict corner action retains the actual returned tensor cell through its proved prism.
`returnedTensorCell_at` and `tensorCell_succ/zero` expose the independent tensor realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorGenerators.lean:27-35"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
def tensorFamilyReturnedPasting (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (((tensorFamily Q).val X).trans (returnedMovement Q X)).RelHomotopy
      ((returnedMovement Q X).trans (returnedTensorCell Q X)) := by
  have hf : (tensorFamily Q).val X = ParameterTensorEvaluationRow.initialCell Q X :=
    ModelUnitRowStrictification.cell_eq laurent.op coefficient (ParameterModels.ambient Q)
      (ParameterLaurentUnit.ambientUnit Q) (returnedTensorModel Q) (returnedTensorIso Q)
      (returnedTensorUnit Q) (returnedTensorIso_unit Q) X
  rw [hf]
  exact returnedPasting Q X

/-- The four actual tensor corner cells on the original polynomial/Laurent square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorGenerators.lean:38-40"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
def tensorSquare (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  diagramSquareMapHomotopy (tensorFamily Q).val (tensorFamily Q).property.1
    (squareFunctor.obj X)

/-- The inherited tensor action satisfies all four explicit quotient-generator formulas. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorGenerators.lean:43-45"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
theorem tensorSquare_generators (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    StrictSquare.MapHomotopy.ConeGeneratorLaw (tensorSquare Q X) (tensorSquare Q X).cone :=
  StrictSquare.MapHomotopy.cone_generatorLaw _

/-- Those tensor values uniquely determine the entire cone action, before index/row transport. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorGenerators.lean:48-52"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
theorem tensorSquare_unique (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy _ _)
    (h : StrictSquare.MapHomotopy.ConeGeneratorLaw (tensorSquare Q X) K) :
    K = (tensorSquare Q X).cone :=
  StrictSquare.MapHomotopy.eq_cone_of_generatorLaw _ K h

/-- Parameter looping acts on the original loop point without exchanging coefficient time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorGenerators.lean:55-59"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
theorem tensorSquare_looped_apply (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r t : unitInterval) (γ : Path _ _) :
    Path.toContinuousMap ((tensorSquare Q X).looped.level n (r, γ)) t =
      (tensorSquare Q X).cone.level n (r, γ t) :=
  StrictSquare.MapHomotopy.looped_apply _ n r t γ

/-- The very Laurent scalar used by the actual tensor corners represents the forward unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ReturnedTensorGenerators.lean:62-70"
  "adaptation" "Original actual returned tensor family and explicit cone generator values."]
theorem coefficient_class (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    CategoryTheory.Waldhausen.KMap
      (boundedAboveFlatPerfectInclusion_isExact (scheme Q (laurent.op.obj X)).toRingedSpace) 1
      (tensorUnitCoefficientKOneClass (scheme Q (laurent.op.obj X))
        (ParameterLaurentUnit.projectedLaurentScalar Q X)) =
      perfectGlobalUnitKOneClass (scheme Q (laurent.op.obj X))
        (ParameterLaurentUnit.projectedLaurentScalar Q X)
        (rankOnePerfectComplex (scheme Q (laurent.op.obj X))) :=
  tensorUnitCoefficientKOneClass_inclusion _ _

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

namespace AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition

attribute [colib_tag "COL-0557"] tensorFamilyReturnedPasting
attribute [colib_tag "COL-0557"] tensorSquare_generators
attribute [colib_tag "COL-0557"] tensorSquare_unique
attribute [colib_tag "COL-0557"] tensorSquare_looped_apply
attribute [colib_tag "COL-0557"] coefficient_class

end AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
