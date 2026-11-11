/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterSupportedTrack
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientNormalization

/-!
# Genuine tensor first rows on the literal supported parameter Model

Evaluation lands in the original supported category. Pullback uses the actual product open-pair
square, after which tensor is applied internally to both zero faces and the middle complex.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow
open GlobalSupportedSection
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual supported product pair at a scheme parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:32"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
def pair (X : Scheme.{u}ᵒᵖ) := GlobalSupportedParameter.pair f X.unop

/-- The original Laurent projection induces this full open-pair square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:35"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
def coefficientPair (X : Scheme.{u}ᵒᵖ) : pair f (laurent.op.obj X) ⟶ pair f X :=
  GlobalSupportedParameter.pairMap f (coefficient.app X).unop

/-- Evaluation of the literal supported parameter Model in its original supported complexes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:39"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
def evaluation (X : Scheme.{u}ᵒᵖ) :
    ((ParameterModels.supported f).obj X).obj.Obj ⥤
      (boundedAboveFlatPerfectSupported (pair f X).hom).FullSubcategory :=
  boundedAboveFlatGlobalSupportedEvaluation (pair f X).hom

/-- The independently constructed first row remains inside the supported target. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:45"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
def firstRow (X : Scheme.{u}ᵒᵖ) :=
  evaluation f X ⋙ boundedAboveFlatPerfectSupportedPullback (coefficientPair f X) ⋙
    boundedAboveFlatPerfectSupportedTensorUnitFirstRow (pair f (laurent.op.obj X)).hom

/-- Both original tensor diagonal entries are genuine zero objects of the supported category. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:50"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
theorem firstRow_zero (X : Scheme.{u}ᵒᵖ)
    (K : ((ParameterModels.supported f).obj X).obj.Obj) (i : Fin 2) :
    IsZero (((boundedAboveFlatPerfectSupportedTensorUnitRows
      (pair f (laurent.op.obj X)).hom).obj
      ((boundedAboveFlatPerfectSupportedPullback (coefficientPair f X)).obj
        ((evaluation f X).obj K))).obj (interval i i le_rfl)) :=
  boundedAboveFlatPerfectSupportedTensorUnitRows_zero _ _ i

/-- The actual row normalization retains both original tensor-zero comparisons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:59"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
def firstRowNormalization (X : Scheme.{u}ᵒᵖ) :
    firstRow f X ≅ evaluation f X ⋙
      tensorSupportedPairNormalizedFunctor (coefficientPair f X) ⋙
        oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen
          (pair f (laurent.op.obj X)).hom) :=
  Functor.isoWhiskerLeft (evaluation f X)
    (tensorSupportedPairFirstRowNormalization (coefficientPair f X))

/-- Forward multiplication by the original projected Laurent unit inside the supported row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:68"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
def firstRowUnit (X : Scheme.{u}ᵒᵖ) :=
  Functor.isoWhiskerLeft (evaluation f X)
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupportedPullback (coefficientPair f X))
      (supportedTensorUnitFirstRowAutomorphism (pair f (laurent.op.obj X)).hom
        (ParameterLaurentUnit.projectedLaurentScalar Q X)))

/-- The whole first supported coefficient prism retains independent unit and row coordinates. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedRow.lean:75"
  "adaptation" "Original supported parameter tensor row and independent prism coordinates."]
theorem prism (X : Scheme.{u}ᵒᵖ) {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ ((ParameterModels.supported f).obj X).obj.Obj)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorSupportedPairNormalizedCoefficientPrism (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) (A ⋙ evaluation f X) τ θ =
      nerveCylinderDiagram (Functor.whiskerLeft (A ⋙ evaluation f X)
        (normalizedWeakTransformation
          (tensorSupportedPair_exact (coefficientPair f X))
          (tensorSupportedPair_exact (coefficientPair f X))
          (tensorSupportedPairAutomorphism (coefficientPair f X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom)) τ ⋙
        suspensionRow (boundedAboveFlatPerfectSupportedWaldhausen
          (pair f (laurent.op.obj X)).hom) θ :=
  tensorSupportedPairNormalizedCoefficientPrism_eq _ _ _ τ θ

end AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow
