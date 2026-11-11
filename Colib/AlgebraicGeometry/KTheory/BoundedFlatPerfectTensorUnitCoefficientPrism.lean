/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientAutomorphism
public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderIsomorphism
public import Colib.KTheory.Waldhausen.Iterated.NaturalHomotopy

/-!
# The first coefficient row times an independent second-input grid

Uncurry the actual automorphism of the independently tensored `0, O, 0` row against an arbitrary
original second-input quotient grid. Its whole diagram is isomorphic to the original tensor-unit
nerve prism followed by the original one-step row. Restricting the first row along an independent
ordinal parameter identifies the whole slice with the original suspension row, including the
actual zero endpoints. The coefficient object-row time and coefficient automorphism-nerve time
remain separate from the second-input grid. No loop transpose or K-one product is implicit here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
      CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The genuine first tensor-row edge uncurried against an unchanged second-input grid. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:34"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
def tensorUnitFirstRowPrism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) (τ : m ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌ :=
  (nerveTimeFunctor n τ).prod' A ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ (tensorUnitFirstRowAutomorphism X r).hom)

/-- The independent coefficient edge is the original cylinder on its genuine tensor rows. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:41"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
theorem tensorUnitFirstRowPrism_eq_nerve (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) (τ : m ⟶ ⦋1⦌) :
    tensorUnitFirstRowPrism X r A τ =
      nerveCylinderDiagram (whiskerLeft A (tensorUnitFirstRowAutomorphism X r).hom) τ :=
  (nerveCylinderDiagram_whiskerLeft (tensorUnitFirstRowAutomorphism X r).hom A τ).symm

/-- The whole coefficient edge, including every crossing, respects the actual first-row iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:48"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
def tensorUnitFirstRowPrismIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) (τ : m ⟶ ⦋1⦌) :
    tensorUnitFirstRowPrism X r A τ ≅
      nerveCylinderDiagram (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom)
      τ ⋙
        oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) := by
  let η := whiskerLeft A (tensorUnitFirstRowAutomorphism X r).hom
  let η' := whiskerRight
    (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom)
    (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
  let e := Functor.isoWhiskerLeft A (tensorUnitFirstRowIso X)
  have h : η ≫ e.hom = e.hom ≫ η' := by
    apply NatTrans.ext
    funext p
    exact congrArg (fun α => α.app (A.obj p))
      (tensorUnitFirstRowAutomorphism_comparison X r)
  exact eqToIso (tensorUnitFirstRowPrism_eq_nerve X r A τ) ≪≫
    nerveCylinderDiagramIso η η' e e h τ ≪≫
      eqToIso (iteratedNerveCylinderDiagram_postcomp
        (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom)
        (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) τ)

/-- The full first-row tensor prism preserves all original second-grid quotient conditions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:70"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
theorem tensorUnitFirstRowPrism_isSimplex₂ (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq A) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).weq
      (tensorUnitFirstRowPrism X r A τ) := by
  rw [tensorUnitFirstRowPrism_eq_nerve]
  exact nerveCylinderDiagram_isSimplex₂
    (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌) _
    (fun _ => (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      ⦋1⦌).weq_iso _ inferInstance)
    (tensorUnitFirstRow_grid X A hA) (tensorUnitFirstRow_grid X A hA) τ

/-- Restrict the actual first coefficient row by a parameter independent of nerve and input grid. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:84"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
def tensorUnitCoefficientPrism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) k :=
  tensorUnitFirstRowPrism X r A τ ⋙ reindex (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) θ

/-- The whole first coefficient slice is the actual tensor prism with the original suspension row.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:92"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
def tensorUnitCoefficientPrismIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorUnitCoefficientPrism X r A τ θ ≅
      nerveCylinderDiagram (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom)
      τ ⋙
        suspensionRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) θ :=
  Functor.isoWhiskerRight (tensorUnitFirstRowPrismIso X r A τ)
    (reindex (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) θ)

/-- Every coefficient ordinal restriction remains exact on the entire second-input prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:102"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
theorem tensorUnitCoefficientPrism_isSimplex₂ (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq A) (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    IsSimplex₂ (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) k).cof
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) k).weq
      (tensorUnitCoefficientPrism X r A τ θ) :=
  (tensorUnitFirstRowPrism_isSimplex₂ X r A hA τ).postcomp _ _
    (reindex_exact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) θ)

/-- First-S reindexing changes only the displayed coefficient-row parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:113"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
theorem tensorUnitCoefficientPrism_reindex (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {l k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) (α : l ⟶ k) :
    tensorUnitCoefficientPrism X r A τ (α ≫ θ) =
      tensorUnitCoefficientPrism X r A τ θ ⋙ reindex (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace) α := by
  rw [tensorUnitCoefficientPrism, reindex_comp]
  rfl

/-- Both coefficient object-row endpoints carry their actual tensor-zero isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientPrism.lean:122"
  "adaptation" "Original coefficient prism and independent ordinal naturality"]
def tensorUnitCoefficientPrismEndpointIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (c : Fin 2) :
    tensorUnitCoefficientPrism X r A τ (SimplexCategory.const k ⦋1⦌ c) ≅
      (Functor.const (Grid₂ n m)).obj (QuotientRows.zero (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace) k) :=
  tensorUnitCoefficientPrismIso X r A τ (SimplexCategory.const k ⦋1⦌ c) ≪≫
    eqToIso (by rw [suspensionRow_const]; rfl)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0545"] tensorUnitCoefficientPrism_isSimplex₂
attribute [colib_tag "COL-0545"] tensorUnitCoefficientPrismEndpointIso

end AlgebraicGeometry.Scheme.Modules
