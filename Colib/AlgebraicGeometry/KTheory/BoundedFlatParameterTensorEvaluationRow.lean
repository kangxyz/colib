/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterOpenTrack
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientNormalization

/-!
# Genuine tensor first rows on the literal parameter ambient Model

The product coefficient map and projected forward Laurent coordinate act on actual evaluated
complexes. Both tensor-zero faces and the independent row and automorphism grid parameters are
retained before comparison with an internal Model row.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
  CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSupportedSection

/-- The actual product scheme underlying a parameter ambient Model. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:29"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def scheme (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) : Scheme.{u} :=
  ((baseProductFunctor (specULiftZIsTerminal.from Q)).op.obj X).unop

/-- The literal product pullback induced by the original Laurent coefficient projection. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:33"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def coefficientMap (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    scheme Q (laurent.op.obj X) ⟶ scheme Q X :=
  ((baseProductFunctor (specULiftZIsTerminal.from Q)).op.map (coefficient.app X)).unop

/-- Original evaluation on the actual parameter ambient Model. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:38"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def evaluation (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((ParameterModels.ambient Q).obj X).obj.Obj ⥤ (boundedAboveFlatPerfectComplex (scheme Q
      X).toRingedSpace).FullSubcategory :=
  boundedAboveFlatGlobalSectionEvaluation ((baseProductFunctor (specULiftZIsTerminal.from
    Q)).op.obj X)

/-- Pull back the evaluated input and apply genuine tensor to the first coefficient row. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:43"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def firstRow (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  evaluation Q X ⋙ boundedAboveFlatPerfectPullback (coefficientMap Q X) ⋙
    boundedAboveFlatPerfectTensorUnitFirstRow (scheme Q (laurent.op.obj X))

/-- Both original diagonal tensor entries are zero objects. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:48"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
theorem firstRow_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (K : ((ParameterModels.ambient Q).obj X).obj.Obj) (i : Fin 2) :
    IsZero (((boundedAboveFlatPerfectTensorUnitRows (scheme Q (laurent.op.obj X))).obj
      ((boundedAboveFlatPerfectPullback (coefficientMap Q X)).obj
        ((evaluation Q X).obj K))).obj (interval i i le_rfl)) :=
  boundedAboveFlatPerfectTensorUnitRows_zero _ _ i

/-- The actual row normalization retains the original tensor-zero comparisons. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:56"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def firstRowNormalization (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    firstRow Q X ≅ evaluation Q X ⋙
      tensorUnitPullbackNormalizedFunctor (coefficientMap Q X) ⋙
        oneEmbedding (boundedAboveFlatPerfectWaldhausen (scheme Q (laurent.op.obj
          X)).toRingedSpace) :=
  Functor.isoWhiskerLeft (evaluation Q X)
    (tensorUnitPullbackFirstRowNormalization (coefficientMap Q X))

/-- Forward multiplication by the original projected Laurent unit on the genuine tensor row. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:64"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def firstRowUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  Functor.isoWhiskerLeft (evaluation Q X)
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback (coefficientMap Q X))
      (tensorUnitFirstRowAutomorphism (scheme Q (laurent.op.obj X))
        (ParameterLaurentUnit.projectedLaurentScalar Q X)))

/-- Whole finite-grid normalization retains separate automorphism and first-row coordinates. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorEvaluationRow.lean:71"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
theorem prism (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ ((ParameterModels.ambient Q).obj X).obj.Obj)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorUnitPullbackNormalizedCoefficientPrism (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) (A ⋙ evaluation Q X) τ θ =
      nerveCylinderDiagram (Functor.whiskerLeft (A ⋙ evaluation Q X)
        (normalizedWeakTransformation
          (boundedAboveFlatPerfectTensorUnitPullback_exact (coefficientMap Q X))
          (boundedAboveFlatPerfectTensorUnitPullback_exact (coefficientMap Q X))
          (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom)) τ ⋙
        suspensionRow (boundedAboveFlatPerfectWaldhausen (scheme Q (laurent.op.obj
          X)).toRingedSpace) θ :=
  tensorUnitPullbackNormalizedCoefficientPrism_eq _ _ _ τ θ

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0546"] prism

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
