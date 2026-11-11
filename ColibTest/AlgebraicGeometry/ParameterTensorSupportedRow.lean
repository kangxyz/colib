/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedRow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRowTest
open ParameterTensorSupportedRow GlobalSupportedSection
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example (X : Scheme.{u}ᵒᵖ)
    (K : ((ParameterModels.supported f).obj X).obj.Obj) (i : Fin 2) :
    IsZero (((boundedAboveFlatPerfectSupportedTensorUnitRows
      (pair f (laurent.op.obj X)).hom).obj
      ((boundedAboveFlatPerfectSupportedPullback (coefficientPair f X)).obj
        ((ParameterTensorSupportedRow.evaluation f X).obj K))).obj (interval i i le_rfl)) :=
  firstRow_zero f X K i

example (X : Scheme.{u}ᵒᵖ) {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ ((ParameterModels.supported f).obj X).obj.Obj)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorSupportedPairNormalizedCoefficientPrism (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) (A ⋙
    ParameterTensorSupportedRow.evaluation f X) τ θ =
      nerveCylinderDiagram (Functor.whiskerLeft (A ⋙ ParameterTensorSupportedRow.evaluation f X)
        (normalizedWeakTransformation
          (tensorSupportedPair_exact (coefficientPair f X))
          (tensorSupportedPair_exact (coefficientPair f X))
          (tensorSupportedPairAutomorphism (coefficientPair f X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom)) τ ⋙
        suspensionRow (boundedAboveFlatPerfectSupportedWaldhausen
          (pair f (laurent.op.obj X)).hom) θ :=
  prism f X A τ θ

example (X : Scheme.{u}ᵒᵖ) :
    firstRow f X ≅ ParameterTensorSupportedRow.evaluation f X ⋙
      tensorSupportedPairNormalizedFunctor (coefficientPair f X) ⋙
        oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen
          (pair f (laurent.op.obj X)).hom) := firstRowNormalization f X

end AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRowTest
