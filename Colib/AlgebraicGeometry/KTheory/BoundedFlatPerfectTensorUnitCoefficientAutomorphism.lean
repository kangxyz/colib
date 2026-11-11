/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientExact

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
open MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The native sheaf-of-modules monoidal structure on the scheme. -/
local instance tensorRowAutomorphismMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
local instance tensorRowAutomorphismPreadditive (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

/-- Actual zero identities and the original structure-module unit in the first coefficient row. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:31"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
def tensorUnitCoefficientRowUnitAt (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (p : Interval ⦋1⦌) :
    (tensorUnitCoefficientRow X).obj p ≅ (tensorUnitCoefficientRow X).obj p := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  change Fin 2 at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact Iso.refl _
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact tensorCoefficientUnitIso X r
  | succ i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hij)
    | succ j => exact Iso.refl _

/-- The genuine coefficient automorphism respects every map of the original zero/unit/zero row. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:52"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem tensorUnitCoefficientRowUnitAt_naturality (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {p q : Interval ⦋1⦌} (f : p ⟶ q) :
    (tensorUnitCoefficientRow X).map f ≫ (tensorUnitCoefficientRowUnitAt X r q).hom =
      (tensorUnitCoefficientRowUnitAt X r p).hom ≫ (tensorUnitCoefficientRow X).map f := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> solve
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact False.elim (Nat.not_succ_le_zero 0 hkl)
  | exact (isZero_zero X.Modules).eq_of_src _ _
  | exact (isZero_zero X.Modules).eq_of_tgt _ _
  | have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

/-- The original coefficient-row unit automorphism before tensor or realization. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:68"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
def tensorUnitCoefficientRowAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientRow X ≅ tensorUnitCoefficientRow X :=
  NatIso.ofComponents (tensorUnitCoefficientRowUnitAt X r)
    (tensorUnitCoefficientRowUnitAt_naturality X r)

/-- First apply actual coefficient tensor, then interchange only the displayed functor indices. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:74"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
def complexTensorUnitRowsAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    complexTensorUnitRows X ≅ complexTensorUnitRows X :=
  (flipFunctor _ _ _).mapIso
    (Functor.isoWhiskerRight (tensorUnitCoefficientRowAutomorphism X r)
      (complexTensorCoefficientFunctor X))

/-- The actual tensor coefficient automorphism lifted to the original bounded-flat diagrams. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:81"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
def boundedAboveFlatPerfectTensorUnitRowsAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectTensorUnitRows X ≅ boundedAboveFlatPerfectTensorUnitRows X :=
  Functor.fullyFaithfulCancelRight
    ((whiskeringRight _ _ _).obj (boundedAboveFlatPerfectComplex X.toRingedSpace).ι)
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
      (complexTensorUnitRowsAutomorphism X r))

/-- Inclusion keeps the original coefficient tensor on every first-row entry and complex degree. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:88"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem tensorUnitRowsAutomorphism_original_f (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) (p : Interval ⦋1⦌) (n
      : ℤ) :
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      (((boundedAboveFlatPerfectTensorUnitRowsAutomorphism X r).hom.app K).app p)).f n =
      ((MonoidalCategory.curriedTensor X.Modules).map
        ((tensorUnitCoefficientRowAutomorphism X r).hom.app p)).app
        (K.obj.X n) := by
  simp only [boundedAboveFlatPerfectTensorUnitRowsAutomorphism,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  let F := (whiskeringRight (Interval ⦋1⦌) ((boundedAboveFlatPerfectComplex
    X.toRingedSpace).FullSubcategory)
    (CochainComplex X.Modules ℤ)).obj (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
  have h := F.map_preimage (X := (boundedAboveFlatPerfectTensorUnitRows X).obj K)
    (Y := (boundedAboveFlatPerfectTensorUnitRows X).obj K)
    ((complexTensorUnitRowsAutomorphism X r).hom.app K.obj)
  exact congrArg (fun η => (η.app p).f n) h

/-- The same actual automorphism in the original first-row Waldhausen category. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:105"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
def tensorUnitFirstRowAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectTensorUnitFirstRow X ≅ boundedAboveFlatPerfectTensorUnitFirstRow X :=
  Functor.fullyFaithfulCancelRight
    (CategoryTheory.Waldhausen.QuotientRows.forget
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌)
    (boundedAboveFlatPerfectTensorUnitRowsAutomorphism X r)

/-- Forgetting row conditions retains the original lifted coefficient tensor. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:111"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem tensorUnitFirstRowAutomorphism_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    ((tensorUnitFirstRowAutomorphism X r).hom.app K).hom =
      (boundedAboveFlatPerfectTensorUnitRowsAutomorphism X r).hom.app K := by
  simp only [tensorUnitFirstRowAutomorphism, Functor.fullyFaithfulCancelRight_hom_app]
  exact (CategoryTheory.Waldhausen.QuotientRows.forget
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).map_preimage _

/-- The whole actual first-row unit square, with both tensor-zero endpoint isomorphisms. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientAutomorphism.lean:119"
  "adaptation" "Actual coefficient row and unchanged exactness/comparison proof."]
theorem tensorUnitFirstRowAutomorphism_comparison (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitFirstRowAutomorphism X r).hom ≫ (tensorUnitFirstRowIso X).hom =
      (tensorUnitFirstRowIso X).hom ≫
        (Functor.isoWhiskerRight (boundedAboveFlatPerfectTensorUnitAutomorphism X r)
          (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).hom := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext p
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;> first
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact (boundedAboveFlatPerfectTensorUnitRows_zero X K 0).eq_of_src _ _
  | change ((tensorUnitFirstRowAutomorphism X r).hom.app K).hom.app
        (interval 0 1 (by decide)) ≫ 𝟙 _ =
      𝟙 _ ≫ (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom.app K
    rw [tensorUnitFirstRowAutomorphism_original]
    simp only [Category.comp_id, Category.id_comp]
    apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
    ext n : 1
    rw [tensorUnitRowsAutomorphism_original_f,
      boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original,
      complexTensorUnitAutomorphism_hom_f]
    rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0544"] tensorUnitFirstRowAutomorphism_comparison

end AlgebraicGeometry.Scheme.Modules
