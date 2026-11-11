/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCellStrictification
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedModel

/-! # Original ParameterTensorReturnedStrictification declarations required by returned tensor
      strictification

Only the selected declarations listed in the source correspondence are migrated here.
The actual row carrier, inclusion, diagonal and iteration remain the original constructions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex GlobalSupportedSection

/-- The whole independent cell at each actual Bass stage, starting from returned tensor data. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorReturnedStrictification.lean:29"
  "adaptation" "Original actual row data and tensor-started recursion"]
def strictifiedIteratedCell (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  SchemeModelRowStrictification.iteratedCell (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

/-- The complete cell equality is proved after the genuine tensor-started recursion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorReturnedStrictification.lean:36"
  "adaptation" "Original actual row data and tensor-started recursion"]
theorem strictifiedIteratedCell_eq (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedIteratedCell Q i X =
      SchemeModelRowSeed.cell (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X :=
  SchemeModelRowStrictification.iteratedCell_eq (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

/-- Normalize the actual tensor-started stage cell before its original cone boundary. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorReturnedStrictification.lean:46"
  "adaptation" "Original actual row data and tensor-started recursion"]
def strictifiedNormalizedForward (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  SchemeModelRowStrictification.normalizedForward (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

/-- Every original normalized forward equals the independently tensor-started forward. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorReturnedStrictification.lean:53"
  "adaptation" "Original actual row data and tensor-started recursion"]
theorem strictifiedNormalizedForward_eq (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedNormalizedForward Q i X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X :=
  SchemeModelRowStrictification.normalizedForward_eq (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0551"] strictifiedNormalizedForward_eq
attribute [colib_tag "COL-0551"] strictifiedIteratedCell
attribute [colib_tag "COL-0551"] strictifiedIteratedCell_eq
attribute [colib_tag "COL-0551"] strictifiedNormalizedForward

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
