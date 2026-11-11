/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientRow

/-!
# Mixed exactness of the actual first tensor row

The independently tensored coefficient row is lifted after proving its actual row predicates.
Its natural comparison with the original one-step embedding transports exactness, including the
all-triples relative cofibration tests and actual pushouts in the second input direction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The genuine first tensor row as an object of the original quotient-row category. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientExact.lean:29"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
def boundedAboveFlatPerfectTensorUnitFirstRow (X : Scheme.{u}) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤ Obj
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌ :=
  (objects (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).lift
    (boundedAboveFlatPerfectTensorUnitRows X) (boundedAboveFlatPerfectTensorUnitRows_isRow X)

/-- The whole first-row comparison is natural in every actual second-input morphism. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientExact.lean:35"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
def tensorUnitFirstRowIso (X : Scheme.{u}) :
    boundedAboveFlatPerfectTensorUnitFirstRow X ≅
      boundedAboveFlatPerfectTensorUnit X ⋙ oneEmbedding (boundedAboveFlatPerfectWaldhausen
        X.toRingedSpace) :=
  NatIso.ofComponents
    (fun K => (objects (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).isoMk
      (tensorUnitRowDiagramIso X K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext p
      rcases p with ⟨⟨i, j⟩, hij⟩
      fin_cases i <;> fin_cases j <;> solve
      | exact False.elim (Nat.not_succ_le_zero 0 hij)
      | exact (boundedAboveFlatPerfectTensorUnitRows_zero X K 0).eq_of_src _ _
      | change (boundedAboveFlatPerfectTensorUnit X).map f ≫ 𝟙 _ =
          𝟙 _ ≫ (boundedAboveFlatPerfectTensorUnit X).map f
        simp)

/-- The actual first-row tensor functor satisfies every original exactness condition. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientExact.lean:55"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem boundedAboveFlatPerfectTensorUnitFirstRow_exact (X : Scheme.{u}) :
    IsExact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).weq
      (boundedAboveFlatPerfectTensorUnitFirstRow X) :=
  ((boundedAboveFlatPerfectTensorUnit_exact X).comp
    (oneEmbedding_exact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).of_iso
      (tensorUnitFirstRowIso X).symm

/-- The mixed first-row/second-input square has the genuine relative pushout cofibration. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientExact.lean:64"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem tensorUnitFirstRow_relative_cof (X : Scheme.{u}) {K L : (boundedAboveFlatPerfectComplex
  X.toRingedSpace).FullSubcategory}
    (f : K ⟶ L) (hf : (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof f)
    (i j k : Fin 2) (hij : i ≤ j) (hjk : j ≤ k) :
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (ExtensionCategory.relativeMap (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        ((horizontalArrow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) i j k hij hjk).map
          ((boundedAboveFlatPerfectTensorUnitFirstRow X).map f))) :=
  ((boundedAboveFlatPerfectTensorUnitFirstRow_exact X).cofibration f hf i j k hij hjk).2

/-- Tensoring any second-input quotient/nerve grid produces a genuine grid of first rows. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientExact.lean:74"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem tensorUnitFirstRow_grid (X : Scheme.{u}) {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq A) :
    IsSimplex₂ (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).weq
      (A ⋙ boundedAboveFlatPerfectTensorUnitFirstRow X) :=
  hA.postcomp _ _ (boundedAboveFlatPerfectTensorUnitFirstRow_exact X)

/-- Every actual second-input pushout is carried to a pushout of the original tensor rows. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientExact.lean:84"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem tensorUnitFirstRow_pushout (X : Scheme.{u}) {A B C D : (boundedAboveFlatPerfectComplex
  X.toRingedSpace).FullSubcategory}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof f) (h : IsPushout f g i j) :
    IsPushout ((boundedAboveFlatPerfectTensorUnitFirstRow X).map f)
      ((boundedAboveFlatPerfectTensorUnitFirstRow X).map g)
      ((boundedAboveFlatPerfectTensorUnitFirstRow X).map i)
      ((boundedAboveFlatPerfectTensorUnitFirstRow X).map j) :=
  (boundedAboveFlatPerfectTensorUnitFirstRow_exact X).pushout hf h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0544"] boundedAboveFlatPerfectTensorUnitFirstRow_exact

end AlgebraicGeometry.Scheme.Modules
