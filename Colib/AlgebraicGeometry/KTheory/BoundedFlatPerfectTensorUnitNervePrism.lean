/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitEdge
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitHomotopy
public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderInterchange

/-!
# A restricted tensor action constructed before the nerve comparison

The actual coefficient arrow `O --μr--> O` is first tensored with an independent input grid by
uncurrying the genuine degreewise coefficient tensor functor. This construction is then identified
with the original nerve-direction cylinder on bounded-flat perfect complexes. Every S-row keeps
its original tensor map, and the original quotient squares remain actual Waldhausen pushouts.

This establishes the raw quotient-grid comparison. Canonical zero normalization, recursive
quotient-row prolongation and the spectrum structure operators are separate consumers.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Uncurry the actual coefficient tensor edge against an independent original complex grid. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitNervePrism.lean:34"
  "adaptation" "Actual tensor edge uncurried on the original independent quotient grid."]
def complexTensorUnitPrism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ CochainComplex X.Modules ℤ)
    (τ : m ⟶ ⦋1⦌) : Grid₂ n m ⥤ CochainComplex X.Modules ℤ :=
  (nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj (complexTensorUnitCoefficientEdge X r)

private theorem complexTensorUnitCoefficientEdge_whisker (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ CochainComplex X.Modules ℤ) :
    complexTensorUnitCoefficientEdge X r ⋙
        (whiskeringLeft _ _ _).obj A =
      ComposableArrows.mk₁ (whiskerLeft A (complexTensorUnitAutomorphism X r).hom) := by
  rw [complexTensorUnitCoefficientEdge_eq]
  apply ComposableArrows.ext₁
    (F := ComposableArrows.mk₁ (complexTensorUnitAutomorphism X r).hom ⋙
      (whiskeringLeft _ _ _).obj A)
    (G := ComposableArrows.mk₁ (whiskerLeft A (complexTensorUnitAutomorphism X r).hom)) rfl rfl
  simp

/-- The independently uncurried tensor edge is the actual original nerve prism. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitNervePrism.lean:52"
  "adaptation" "Actual tensor edge uncurried on the original independent quotient grid."]
theorem complexTensorUnitPrism_eq_nerve (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ CochainComplex X.Modules ℤ)
    (τ : m ⟶ ⦋1⦌) :
    complexTensorUnitPrism X r A τ =
      nerveCylinderDiagram (whiskerLeft A (complexTensorUnitAutomorphism X r).hom) τ := by
  unfold complexTensorUnitPrism nerveCylinderDiagram
  rw [← complexTensorUnitCoefficientEdge_whisker]
  rfl

/-- The bounded-flat nerve cylinder retains the independent tensor-edge construction after the
literal inclusion into ordinary complexes. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitNervePrism.lean:63"
  "adaptation" "Actual tensor edge uncurried on the original independent quotient grid."]
theorem boundedAboveFlatPerfectTensorUnitPrism_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom) τ ⋙
        (boundedAboveFlatPerfectComplex X.toRingedSpace).ι =
      complexTensorUnitPrism X r (A ⋙ (boundedAboveFlatPerfectComplex X.toRingedSpace).ι) τ := by
  rw [← iteratedNerveCylinderDiagram_postcomp, complexTensorUnitPrism_eq_nerve]
  congr 1
  apply NatTrans.ext
  funext p
  exact boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original X r (A.obj p)

/-- Every input quotient grid remains a genuine grid under the restricted tensor-unit prism. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitNervePrism.lean:75"
  "adaptation" "Actual tensor edge uncurried on the original independent quotient grid."]
theorem boundedAboveFlatPerfectTensorUnitPrism_isSimplex₂ (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq A) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (nerveCylinderDiagram
        (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom) τ) :=
  nerveCylinderDiagram_isSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) _
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (hA.postcomp _ _ (boundedAboveFlatPerfectTensorUnit_exact X))
    (hA.postcomp _ _ (boundedAboveFlatPerfectTensorUnit_exact X)) τ

/-- Along each original S-row the tensor prism uses exactly its selected endpoint map. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitNervePrism.lean:88"
  "adaptation" "Actual tensor edge uncurried on the original independent quotient grid."]
theorem boundedAboveFlatPerfectTensorUnitPrism_rowMap (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) (τ : m ⟶ ⦋1⦌)
    (t : Fin (m.len + 1)) (i j k l : Fin (n.len + 1)) (hij : i ≤ j) (hkl : k ≤ l)
    (f : grid₂ t i j hij ⟶ grid₂ t k l hkl) :
    (nerveCylinderDiagram
      (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom) τ).map f =
      ((ComposableArrows.mk₁
        (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom)).obj
          (τ.toOrderHom t)).map f :=
  nerveCylinderDiagram_rowMap _ τ t i j k l hij hkl f

/-- At the original diagonal S-level, the entire cylinder is the tensor-edge times input-grid
construction, with the original simplex and nerve time retained. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitNervePrism.lean:101"
  "adaptation" "Actual tensor edge uncurried on the original independent quotient grid."]
theorem boundedAboveFlatPerfectTensorUnitCylinder_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq).obj n) (τ : (Δ[1]).obj n) :
    ((weakNaturalTransformationCylinder (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        (boundedAboveFlatPerfectTensorUnit_exact X)
      (boundedAboveFlatPerfectTensorUnit_exact X)
      (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom
      (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)).app
        n (A, τ)).val ⋙
        (boundedAboveFlatPerfectComplex X.toRingedSpace).ι =
      complexTensorUnitPrism X r (A.val ⋙ (boundedAboveFlatPerfectComplex X.toRingedSpace).ι)
        τ.down :=
  boundedAboveFlatPerfectTensorUnitPrism_original X r A.val τ.down

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0543"] boundedAboveFlatPerfectTensorUnitPrism_original

end AlgebraicGeometry.Scheme.Modules
