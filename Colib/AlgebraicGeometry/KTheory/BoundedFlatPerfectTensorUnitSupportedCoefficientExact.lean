/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientRow

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
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open AlgebraicGeometry.RingedSpace
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- The genuine first tensor row as an object of the original quotient-row category. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientExact.l\
    ean:30"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
def boundedAboveFlatPerfectSupportedTensorUnitFirstRow :
    (boundedAboveFlatPerfectSupported ι).FullSubcategory ⥤
      Obj (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌ :=
  (objects (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).lift
    (boundedAboveFlatPerfectSupportedTensorUnitRows ι)
    (boundedAboveFlatPerfectSupportedTensorUnitRows_isRow ι)

/-- The whole first-row comparison is natural in every actual second-input morphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientExact.l\
    ean:38"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
def supportedTensorUnitFirstRowIso :
    boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι ≅
      boundedAboveFlatPerfectSupportedTensorUnit ι ⋙
        oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen ι) :=
  NatIso.ofComponents
    (fun K => (objects (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).isoMk
      (supportedTensorUnitRowDiagramIso ι K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext p
      rcases p with ⟨⟨i, j⟩, hij⟩
      fin_cases i <;> fin_cases j <;> solve
      | exact False.elim (Nat.not_succ_le_zero 0 hij)
      | exact (boundedAboveFlatPerfectSupportedTensorUnitRows_zero ι K 0).eq_of_src _ _
      | change (boundedAboveFlatPerfectSupportedTensorUnit ι).map f ≫ 𝟙 _ =
          𝟙 _ ≫ (boundedAboveFlatPerfectSupportedTensorUnit ι).map f
        simp)

/-- The actual first-row tensor functor satisfies every original exactness condition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientExact.l\
    ean:59"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem boundedAboveFlatPerfectSupportedTensorUnitFirstRow_exact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen ι).weq
      (waldhausenStructure (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).weq
      (boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι) :=
  ((boundedAboveFlatPerfectSupportedTensorUnit_exact ι).comp
    (oneEmbedding_exact (boundedAboveFlatPerfectSupportedWaldhausen ι))).of_iso
      (supportedTensorUnitFirstRowIso ι).symm

/-- The mixed first-row/second-input square has the genuine relative pushout cofibration. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientExact.l\
    ean:70"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem supportedTensorUnitFirstRow_relative_cof
    {K L : (boundedAboveFlatPerfectSupported ι).FullSubcategory}
    (f : K ⟶ L) (hf : (boundedAboveFlatPerfectSupportedWaldhausen ι).cof f)
    (i j k : Fin 2) (hij : i ≤ j) (hjk : j ≤ k) :
    (boundedAboveFlatPerfectSupportedWaldhausen ι).cof
      (ExtensionCategory.relativeMap (boundedAboveFlatPerfectSupportedWaldhausen ι)
        ((horizontalArrow (boundedAboveFlatPerfectSupportedWaldhausen ι) i j k hij hjk).map
          ((boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι).map f))) :=
  ((boundedAboveFlatPerfectSupportedTensorUnitFirstRow_exact ι).cofibration f hf i j k hij hjk).2

/-- Tensoring any second-input quotient/nerve grid produces a genuine grid of first rows. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientExact.l\
    ean:81"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem supportedTensorUnitFirstRow_grid {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectSupported ι).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectSupportedWaldhausen ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen ι).weq A) :
    IsSimplex₂ (waldhausenStructure (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).weq
      (A ⋙ boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι) :=
  hA.postcomp _ _ (boundedAboveFlatPerfectSupportedTensorUnitFirstRow_exact ι)

/-- Every actual second-input pushout is carried to a pushout of the original tensor rows. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientExact.l\
    ean:91"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem supportedTensorUnitFirstRow_pushout
    {A B C D : (boundedAboveFlatPerfectSupported ι).FullSubcategory}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : (boundedAboveFlatPerfectSupportedWaldhausen ι).cof f) (h : IsPushout f g i j) :
    IsPushout ((boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι).map f)
      ((boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι).map g)
      ((boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι).map i)
      ((boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι).map j) :=
  (boundedAboveFlatPerfectSupportedTensorUnitFirstRow_exact ι).pushout hf h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0561"] boundedAboveFlatPerfectSupportedTensorUnitFirstRow_exact

end AlgebraicGeometry.Scheme.Modules
