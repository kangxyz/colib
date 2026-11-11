/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientPrismNaturality

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.Scheme.Modules
open scoped Simplicial
noncomputable section
universe u v u' v'

example {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F G : C ⥤ D} (η : F ⟶ G)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ C) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft A η) τ =
      (nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj (ComposableArrows.mk₁ η) :=
  nerveCylinderDiagram_whiskerLeft η A τ

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) (τ : m ⟶ ⦋1⦌) :
    tensorUnitFirstRowPrism X r A τ =
      nerveCylinderDiagram (whiskerLeft A (tensorUnitFirstRowAutomorphism X r).hom) τ :=
  tensorUnitFirstRowPrism_eq_nerve X r A τ

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq A) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⦋1⦌).weq
      (tensorUnitFirstRowPrism X r A τ) :=
  tensorUnitFirstRowPrism_isSimplex₂ X r A hA τ

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (c : Fin 2) :
    tensorUnitCoefficientPrism X r A τ (SimplexCategory.const k ⦋1⦌ c) ≅
      (Functor.const (Grid₂ n m)).obj (QuotientRows.zero (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace) k) :=
  tensorUnitCoefficientPrismEndpointIso X r A τ c

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (hA : IsSimplex₂ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq A) (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    IsSimplex₂ (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) k).cof
      (waldhausenStructure (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) k).weq
      (tensorUnitCoefficientPrism X r A τ θ) :=
  tensorUnitCoefficientPrism_isSimplex₂ X r A hA τ θ

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m n' m' : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (α : n' ⟶ n) (β : m' ⟶ m) :
    tensorUnitFirstRowPrism X r (gridMap₂ α β ⋙ A) (β ≫ τ) =
      gridMap₂ α β ⋙ tensorUnitFirstRowPrism X r A τ :=
  tensorUnitFirstRowPrism_precomp X r A τ α β

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m n' m' : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) (α : n' ⟶ n) (β : m' ⟶ m) :
    tensorUnitCoefficientPrism X r (gridMap₂ α β ⋙ A) (β ≫ τ) θ =
      gridMap₂ α β ⋙ tensorUnitCoefficientPrism X r A τ θ :=
  tensorUnitCoefficientPrism_precomp X r A τ θ α β

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k l n m n' m' : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) (ρ : l ⟶ k) (α : n' ⟶ n) (β : m' ⟶ m) :
    tensorUnitCoefficientPrism X r (gridMap₂ α β ⋙ A) (β ≫ τ) (ρ ≫ θ) =
      gridMap₂ α β ⋙ tensorUnitCoefficientPrism X r A τ θ ⋙
        reindex (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ρ :=
  tensorUnitCoefficientPrism_reindex_all X r A τ θ ρ α β

