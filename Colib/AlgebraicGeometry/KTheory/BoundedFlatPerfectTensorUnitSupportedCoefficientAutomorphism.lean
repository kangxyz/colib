/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientAutomorphism

/-!
# The original unit automorphism on the first coefficient tensor row

The coefficient automorphism acts as the identity on both original zero modules and as the
original multiplication map on the structure module. Applying the genuine coefficient tensor
functor gives an automorphism of the independently constructed tensor row. The whole row square
with the canonical one-step row retains both actual tensor-zero endpoint isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open AlgebraicGeometry.RingedSpace
open scoped Simplicial ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Native sheaf tensor on the unchanged supported ambient module category. -/
local instance supportedRowAutomorphismMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
/-- Native additive tensor used in every original complex degree. -/
local instance supportedRowAutomorphismPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]


/-- Original coefficient multiplication lifted entrywise to the actual supported row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientAutomor\
    phism.lean:33"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
def boundedAboveFlatPerfectSupportedTensorUnitRowsAutomorphism (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectSupportedTensorUnitRows ι ≅
      boundedAboveFlatPerfectSupportedTensorUnitRows ι :=
  NatIso.ofComponents (fun K => NatIso.ofComponents
    (fun p => (boundedAboveFlatPerfectSupported ι).isoMk
      (((complexTensorUnitRowsAutomorphism X r).app K.obj).app p))
    (by
      intro p q f
      apply (boundedAboveFlatPerfectSupported ι).ι.map_injective
      exact ((complexTensorUnitRowsAutomorphism X r).hom.app K.obj).naturality f))
    (by
      intro K L f
      apply NatTrans.ext
      funext p
      apply (boundedAboveFlatPerfectSupported ι).ι.map_injective
      exact NatTrans.congr_app ((complexTensorUnitRowsAutomorphism X r).hom.naturality f.hom) p)

/-- Inclusion retains every original tensor multiplication entry and complex degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientAutomor\
    phism.lean:50"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem supportedTensorUnitRowsAutomorphism_original_f (r : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory) (p : Interval ⦋1⦌) (n : ℤ) :
    ((boundedAboveFlatPerfectSupported ι).ι.map
      (((boundedAboveFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.app K).app p)).f n =
      ((MonoidalCategory.curriedTensor X.Modules).map
        ((tensorUnitCoefficientRowAutomorphism X r).hom.app p)).app
        (K.obj.X n) := rfl

/-- The genuine multiplication in the original supported quotient-row category. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientAutomor\
    phism.lean:58"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
def supportedTensorUnitFirstRowAutomorphism (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι ≅
      boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι :=
  NatIso.ofComponents
    (fun K => (objects (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).isoMk
      ((boundedAboveFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).app K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (boundedAboveFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.naturality f)

/-- Forgetting only the row predicates keeps the original supported tensor multiplication. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientAutomor\
    phism.lean:69"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem supportedTensorUnitFirstRowAutomorphism_original (r : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory) :
    ((supportedTensorUnitFirstRowAutomorphism ι r).hom.app K).hom =
      (boundedAboveFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.app K := rfl

/-- The whole actual first-row unit square, with both tensor-zero endpoint isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientAutomor\
    phism.lean:75"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem supportedTensorUnitFirstRowAutomorphism_comparison (r : (Γ(X, ⊤))ˣ) :
    (supportedTensorUnitFirstRowAutomorphism ι r).hom ≫ (supportedTensorUnitFirstRowIso ι).hom =
      (supportedTensorUnitFirstRowIso ι).hom ≫
        (Functor.isoWhiskerRight (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism ι r)
          (oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen ι))).hom := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext p
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;> first
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact (boundedAboveFlatPerfectSupportedTensorUnitRows_zero ι K 0).eq_of_src _ _
  | change ((supportedTensorUnitFirstRowAutomorphism ι r).hom.app K).hom.app
        (interval 0 1 (by decide)) ≫ 𝟙 _ =
      𝟙 _ ≫ (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism ι r).hom.app K
    rw [supportedTensorUnitFirstRowAutomorphism_original]
    simp only [Category.comp_id, Category.id_comp]
    apply (boundedAboveFlatPerfectSupported ι).ι.map_injective
    ext n : 1
    rw [supportedTensorUnitRowsAutomorphism_original_f,
      boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_hom_original,
      complexTensorUnitAutomorphism_hom_f]
    rfl

end AlgebraicGeometry.Scheme.Modules
