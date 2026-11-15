/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Products
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition

/-! # The original diagonals and graphs of smooth schemes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- The original scheme diagonal, viewed in the smooth site. -/
def productDiagonal (X : SmoothSite S) : X ⟶ product X X :=
  productLift (𝟙 X) (𝟙 X)

@[reassoc (attr := simp)]
theorem productDiagonal_fst (X : SmoothSite S) :
    productDiagonal X ≫ productFst X X = 𝟙 X :=
  productLift_fst _ _

@[reassoc (attr := simp)]
theorem productDiagonal_snd (X : SmoothSite S) :
    productDiagonal X ≫ productSnd X X = 𝟙 X :=
  productLift_snd _ _

theorem productDiagonal_left (X : SmoothSite S) :
    (productDiagonal X).left = pullback.diagonal X.hom := by
  apply pullback.hom_ext
  · exact (congrArg (fun f => f.left) (productDiagonal_fst X)).trans
      (pullback.diagonal_fst X.hom).symm
  · exact (congrArg (fun f => f.left) (productDiagonal_snd X)).trans
      (pullback.diagonal_snd X.hom).symm

instance (X : SmoothSite S) : IsClosedImmersion (productDiagonal X).left := by
  rw [productDiagonal_left]
  exact IsSeparated.isClosedImmersion_diagonal (f := X.hom)

/-- The literal square of a pure-dimensional smooth scheme has twice its dimension. -/
theorem relativeDimension_smoothSquare (X : SmoothSite S) {d : ℕ} (h : RelativeDimension X.hom d) :
    RelativeDimension (product X X).hom (d + d) := by
  let q : (product X X).left ⟶ X.left := pullback.fst X.hom X.hom
  let : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom X.hom))
  let : Flat q := inferInstanceAs (Flat (pullback.fst X.hom X.hom))
  have hq : RelativeDimension q d :=
    RelativeDimension.of_isPullback (IsPullback.of_hasPullback X.hom X.hom).flip h
  exact RelativeDimension.comp_of_flat q X.hom hq h

/-- The original graph of a smooth-site map, as a map into the scheme product. -/
abbrev productGraph {X Y : SmoothSite S} (f : X ⟶ Y) : X ⟶ product X Y :=
  productLift (𝟙 X) f

/-- Pulling back the actual diagonal along the first-factor map gives
the original graph, including its full scheme structure. -/
theorem isPullback_productGraph_productDiagonal {X Y : SmoothSite S} (f : X ⟶ Y) :
    IsPullback f.left (productGraph f).left (productDiagonal Y).left
      (productMap f (𝟙 Y)).left := by
  let p : (product X Y).left ⟶ X.left := (productFst X Y).left
  let q : (product X Y).left ⟶ Y.left := (productSnd X Y).left
  let p' : (product Y Y).left ⟶ Y.left := (productFst Y Y).left
  let q' : (product Y Y).left ⟶ Y.left := (productSnd Y Y).left
  let d := (productDiagonal Y).left
  let j := (productGraph f).left
  let m := (productMap f (𝟙 Y)).left
  have hp : j ≫ p = 𝟙 X.left := congrArg (fun a => a.left) (productLift_fst (𝟙 X) f)
  have hq : j ≫ q = f.left := congrArg (fun a => a.left) (productLift_snd (𝟙 X) f)
  have hd₁ : d ≫ p' = 𝟙 Y.left := congrArg (fun a => a.left) (productDiagonal_fst Y)
  have hd₂ : d ≫ q' = 𝟙 Y.left := congrArg (fun a => a.left) (productDiagonal_snd Y)
  have hm₁ : m ≫ p' = p ≫ f.left := congrArg (fun a => a.left) (productMap_fst f (𝟙 Y))
  have hm₂ : m ≫ q' = q := by
    exact (congrArg (fun a => a.left) (productMap_snd f (𝟙 Y))).trans (Category.comp_id _)
  have hw : f.left ≫ d = j ≫ m := by
    apply pullback.hom_ext
    · change (f.left ≫ d) ≫ p' = (j ≫ m) ≫ p'
      simp only [Category.assoc, hd₁, hm₁, ← Category.assoc j p, hp,
        Category.comp_id, Category.id_comp]
    · change (f.left ≫ d) ≫ q' = (j ≫ m) ≫ q'
      simp only [Category.assoc, hd₂, hm₂, hq, Category.comp_id]
  have hcone (a : PullbackCone d m) :
      a.fst = (a.snd ≫ p) ≫ f.left ∧ a.fst = a.snd ≫ q := by
    constructor
    · have h := congrArg (fun g => g ≫ p') a.condition
      simpa only [Category.assoc, hd₁, hm₁, Category.comp_id] using h
    · have h := congrArg (fun g => g ≫ q') a.condition
      simpa only [Category.assoc, hd₂, hm₂, Category.comp_id] using h
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw (fun a => a.snd ≫ p) ?_ ?_ ?_)
  · exact fun a => (hcone a).1.symm
  · intro a
    apply pullback.hom_ext
    · change ((a.snd ≫ p) ≫ j) ≫ p = a.snd ≫ p
      simp only [Category.assoc, hp, Category.comp_id]
    · change ((a.snd ≫ p) ≫ j) ≫ q = a.snd ≫ q
      rw [Category.assoc, hq, ← (hcone a).1, (hcone a).2]
  · intro a g _ hg
    exact (Category.comp_id g).symm.trans
      ((congrArg (g ≫ ·) hp.symm).trans
        ((Category.assoc g j p).symm.trans (congrArg (· ≫ p) hg)))

instance {X Y : SmoothSite S} (f : X ⟶ Y) : IsClosedImmersion (productGraph f).left :=
  MorphismProperty.of_isPullback (isPullback_productGraph_productDiagonal f)
    (inferInstance : IsClosedImmersion (productDiagonal Y).left)

end AlgebraicGeometry.Scheme.SmoothSite
