/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Normalization
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.TorusInversion
public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
import Mathlib.Tactic.Abel

/-!
# The two torus factors on signed finite correspondences

In right-factor coordinates the swap exchanges the two actual unit projectors.
Inversion on the new outer factor commutes with every exterior correspondence
by the native parameter-map naturality. Its two occurrences therefore cancel
on the extension by the outer reduced torus. These are the signed identities
in the proof of Voevodsky's Lemma 4.7.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "F" => Cor.parameterProduct Gₖ
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
local notation "uₖ" => toBase Gₖ ≫ torusOne Sₖ

/-- The actual graph swapping the last two torus factors and retaining the base. -/
abbrev torusDoubleSwap (X : Cor k) : ((F).obj ((F).obj X)) ⟶ ((F).obj ((F).obj X)) :=
  γ (productSwapLast X.toSmoothSite Gₖ Gₖ)

/-- The graph of inversion on the last torus factor, with the first factor retained. -/
abbrev torusDoubleInversion (X : Cor k) : ((F).obj ((F).obj X)) ⟶ ((F).obj ((F).obj X)) :=
  (Cor.parameterProductMap (torusInversion Sₖ)).app ((F).obj X)

/-- The native double product map retaining both torus coordinates. -/
def torusDoubleBaseMap {X Y : SmoothSite (Spec (CommRingCat.of k))} (f : X ⟶ Y) :
    SmoothSite.product (SmoothSite.product X Gₖ) Gₖ ⟶
      SmoothSite.product (SmoothSite.product Y Gₖ) Gₖ :=
  SmoothSite.productMap (SmoothSite.productMap f (𝟙 Gₖ)) (𝟙 Gₖ)

/-- Applying the signed exterior identity twice to a graph gives the actual double product map. -/
theorem parameterProduct_twice_graph {X Y : SmoothSite (Spec (CommRingCat.of k))} (f : X ⟶ Y) :
    (F).map ((F).map (γ f)) = γ (torusDoubleBaseMap k f) := by
  simp only [Cor.parameterProduct_graph, torusDoubleBaseMap]

set_option quotPrecheck false in
local notation "inner(" X ")" => ((F).map (torusUnitProjector k X))
set_option quotPrecheck false in
local notation "outer(" X ")" => torusUnitProjector k ((F).obj X)

/-- Project away from both unit axes on the native double torus product. -/
def torusDoubleReduction (X : Cor k) : ((F).obj ((F).obj X)) ⟶ ((F).obj ((F).obj X)) :=
  (𝟙 _ - inner(X)) ≫ (𝟙 _ - outer(X))

/-- Extend the signed correspondence by the actual complementary outer unit idempotent. -/
def torusOuterReducedExtension {X Y : Cor k} (α : (F).obj X ⟶ (F).obj Y) :
    ((F).obj ((F).obj X)) ⟶ ((F).obj ((F).obj Y)) :=
  (F).map α ≫ (𝟙 _ - outer(Y))

/-- Place the new reduced factor before the original one in the same native product. -/
def torusInnerReducedExtension {X Y : Cor k} (α : (F).obj X ⟶ (F).obj Y) :
    ((F).obj ((F).obj X)) ⟶ ((F).obj ((F).obj Y)) :=
  torusDoubleSwap k X ≫ torusOuterReducedExtension k α ≫ torusDoubleSwap k Y

/-- The outer reduced extension commutes with restriction by an ordinary base graph. -/
theorem torusOuterReducedExtension_graph_precomp {X Y Z : Cor k}
    (f : X.toSmoothSite ⟶ Y.toSmoothSite) (α : (F).obj Y ⟶ (F).obj Z) :
    γ (torusDoubleBaseMap k f) ≫ torusOuterReducedExtension k α =
      torusOuterReducedExtension k ((F).map (γ f) ≫ α) := by
  simp only [← parameterProduct_twice_graph, torusOuterReducedExtension, Functor.map_comp,
    Category.assoc]

/-- The outer inverse commutes with the original double product graph. -/
theorem torusDoubleInversion_baseMap {X Y : Cor k} (f : X.toSmoothSite ⟶ Y.toSmoothSite) :
    γ (torusDoubleBaseMap k f) ≫ torusDoubleInversion k Y =
      torusDoubleInversion k X ≫ γ (torusDoubleBaseMap k f) := by
  rw [← parameterProduct_twice_graph]
  exact (Cor.parameterProductMap (torusInversion Sₖ)).naturality ((F).map (γ f))

private theorem torusUnitProjector_eq_productMap (X : Cor k) :
    torusUnitProjector k X = γ (SmoothSite.productMap (𝟙 X.toSmoothSite) uₖ) := by
  rw [torusUnitProjector_eq_graph]
  apply (Cor.graphFunctor k).congr_map
  apply product_hom_ext <;> simp [unitSection, Category.assoc]

/-- The original double swap carries the outer unit projector to the inner one. -/
theorem torusDoubleSwap_comp_outer (X : Cor k) :
    torusDoubleSwap k X ≫ outer(X) = inner(X) ≫ torusDoubleSwap k X := by
  rw [torusUnitProjector_eq_productMap, torusUnitProjector_eq_productMap,
    Cor.parameterProduct_graph, ← Functor.map_comp, ← Functor.map_comp]
  apply (Cor.graphFunctor k).congr_map
  let s := productSwapLast X.toSmoothSite Gₖ Gₖ
  change s ≫ SmoothSite.productMap (𝟙 (X.toSmoothSite.product Gₖ)) uₖ =
    SmoothSite.productMap (SmoothSite.productMap (𝟙 X.toSmoothSite) uₖ) (𝟙 Gₖ) ≫ s
  have h := (productSwapLast_naturality X.toSmoothSite Gₖ Gₖ (𝟙 X.toSmoothSite) uₖ (𝟙 Gₖ)).symm
  rw [SmoothSite.productMap_id] at h
  exact h

private theorem torusDoubleSwap_comp_inner (X : Cor k) :
    torusDoubleSwap k X ≫ inner(X) = outer(X) ≫ torusDoubleSwap k X := by
  rw [torusUnitProjector_eq_productMap, torusUnitProjector_eq_productMap,
    Cor.parameterProduct_graph, ← Functor.map_comp, ← Functor.map_comp]
  apply (Cor.graphFunctor k).congr_map
  let s := productSwapLast X.toSmoothSite Gₖ Gₖ
  change s ≫ SmoothSite.productMap (SmoothSite.productMap (𝟙 X.toSmoothSite) uₖ) (𝟙 Gₖ) =
    SmoothSite.productMap (𝟙 (X.toSmoothSite.product Gₖ)) uₖ ≫ s
  have h := (productSwapLast_naturality X.toSmoothSite Gₖ Gₖ (𝟙 X.toSmoothSite) (𝟙 Gₖ) uₖ).symm
  rw [SmoothSite.productMap_id] at h
  exact h

private theorem complement_naturality {X Y : Cor k} (f : X ⟶ Y) (e : X ⟶ X) (e' : Y ⟶ Y)
    (h : f ≫ e' = e ≫ f) : f ≫ (𝟙 _ - e') = (𝟙 _ - e) ≫ f := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp, h]

private theorem unitComplements_commute (X : Cor k) :
    (𝟙 _ - inner(X)) ≫ (𝟙 _ - outer(X)) = (𝟙 _ - outer(X)) ≫ (𝟙 _ - inner(X)) := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
    torusUnitProjector_naturality k (torusUnitProjector k X)]
  abel

/-- The graph with first torus coordinate one is killed by the double reduction. -/
theorem graph_doubleUnit_first_comp_reduction
    {U X : SmoothSite (Spec (CommRingCat.of k))} (p : U ⟶ X) (q : U ⟶ Gₖ) :
    γ (productLift (productLift p (toBase U ≫ torusOne Sₖ)) q) ≫
      torusDoubleReduction k (Cor.mk X) = 0 := by
  let f := productLift (productLift p (toBase U ≫ torusOne Sₖ)) q
  let a : Cor.mk U ⟶ (F).obj ((F).obj (Cor.mk X)) := γ f
  have h : a ≫ inner(Cor.mk X) = a := by
    change γ f ≫ inner(Cor.mk X) = γ f
    rw [torusUnitProjector_eq_productMap, Cor.parameterProduct_graph, ← Functor.map_comp]
    apply (Cor.graphFunctor k).congr_map
    apply product_hom_ext
    · apply product_hom_ext <;> simp [f, Category.assoc]
    · simp [f]
  have hz : a ≫ (𝟙 _ - inner(Cor.mk X)) = 0 := by
    simp only [Preadditive.comp_sub, Category.comp_id, h, sub_self]
  change a ≫ torusDoubleReduction k (Cor.mk X) = 0
  rw [torusDoubleReduction, ← Category.assoc, hz, CategoryTheory.Limits.zero_comp]

/-- The graph with last torus coordinate one is killed by the double reduction. -/
theorem graph_doubleUnit_last_comp_reduction
    {U X : SmoothSite (Spec (CommRingCat.of k))} (p : U ⟶ X) (q : U ⟶ Gₖ) :
    γ (productLift (productLift p q) (toBase U ≫ torusOne Sₖ)) ≫
      torusDoubleReduction k (Cor.mk X) = 0 := by
  let f := productLift (productLift p q) (toBase U ≫ torusOne Sₖ)
  let a : Cor.mk U ⟶ (F).obj ((F).obj (Cor.mk X)) := γ f
  have h : a ≫ outer(Cor.mk X) = a := by
    change γ f ≫ outer(Cor.mk X) = γ f
    rw [torusUnitProjector_eq_productMap, ← Functor.map_comp]
    apply (Cor.graphFunctor k).congr_map
    apply product_hom_ext
    · simp [f, Category.assoc]
    · let M := X.product Gₖ
      change (f ≫ SmoothSite.productMap (𝟙 M) uₖ) ≫ productSnd M Gₖ = f ≫ productSnd M Gₖ
      calc
        _ = f ≫ productSnd M Gₖ ≫ uₖ := by rw [Category.assoc, SmoothSite.productMap_snd]
        _ = toBase U ≫ torusOne Sₖ := by simp only [comp_toBase_assoc]
        _ = _ := (SmoothSite.productLift_snd (productLift p q) (toBase U ≫ torusOne Sₖ)).symm
  have hz : a ≫ (𝟙 _ - outer(Cor.mk X)) = 0 := by
    simp only [Preadditive.comp_sub, Category.comp_id, h, sub_self]
  change a ≫ torusDoubleReduction k (Cor.mk X) = 0
  rw [torusDoubleReduction, unitComplements_commute, ← Category.assoc, hz,
    CategoryTheory.Limits.zero_comp]

/-- Swapping the two torus factors preserves the actual double reduction. -/
theorem torusDoubleSwap_reduction (X : Cor k) :
    torusDoubleSwap k X ≫ torusDoubleReduction k X =
      torusDoubleReduction k X ≫ torusDoubleSwap k X := by
  rw [torusDoubleReduction, ← Category.assoc,
    complement_naturality k _ _ _ (torusDoubleSwap_comp_inner k X), Category.assoc,
    complement_naturality k _ _ _ (torusDoubleSwap_comp_outer k X), ← Category.assoc,
    ← unitComplements_commute]

/-- The actual double swap is natural in the original smooth base. -/
theorem torusDoubleSwap_baseMap {X Y : Cor k} (f : X.toSmoothSite ⟶ Y.toSmoothSite) :
    γ (torusDoubleBaseMap k f) ≫ torusDoubleSwap k Y =
      torusDoubleSwap k X ≫ γ (torusDoubleBaseMap k f) := by
  change γ (torusDoubleBaseMap k f) ≫ γ (productSwapLast Y.toSmoothSite Gₖ Gₖ) =
    γ (productSwapLast X.toSmoothSite Gₖ Gₖ) ≫ γ (torusDoubleBaseMap k f)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (Cor.graphFunctor k).congr_map
    (productSwapLast_naturality X.toSmoothSite Gₖ Gₖ f (𝟙 Gₖ) (𝟙 Gₖ))

/-- Both unit reductions commute with the original double product graph. -/
theorem torusDoubleReduction_baseMap {X Y : Cor k} (f : X.toSmoothSite ⟶ Y.toSmoothSite) :
    γ (torusDoubleBaseMap k f) ≫ torusDoubleReduction k Y =
      torusDoubleReduction k X ≫ γ (torusDoubleBaseMap k f) := by
  let a : (F).obj ((F).obj X) ⟶ (F).obj ((F).obj Y) := γ (torusDoubleBaseMap k f)
  let b : X ⟶ Y := γ f
  have ha : a = (F).map ((F).map b) := (parameterProduct_twice_graph k f).symm
  have ho : a ≫ outer(Y) = outer(X) ≫ a := by
    rw [ha]
    exact torusUnitProjector_naturality k ((F).map b)
  have hi : a ≫ inner(Y) = inner(X) ≫ a := by
    rw [ha]
    simpa only [Functor.map_comp] using congrArg (F).map (torusUnitProjector_naturality k b)
  change a ≫ ((𝟙 _ - inner(Y)) ≫ (𝟙 _ - outer(Y))) =
    ((𝟙 _ - inner(X)) ≫ (𝟙 _ - outer(X))) ≫ a
  rw [← Category.assoc, complement_naturality k _ _ _ hi, Category.assoc,
    complement_naturality k _ _ _ ho, ← Category.assoc]

private theorem torusDoubleInversion_comp_outer (X : Cor k) :
    torusDoubleInversion k X ≫ outer(X) = outer(X) ≫ torusDoubleInversion k X := by
  let U := ((F).obj X).toSmoothSite
  have h₁ : torusInversion Sₖ ≫ uₖ = uₖ := by rw [comp_toBase_assoc]
  have h₂ : uₖ ≫ torusInversion Sₖ = uₖ := by
    rw [Category.assoc, torusOne_comp_torusInversion]
  rw [torusUnitProjector_eq_productMap]
  change γ (SmoothSite.productMap (𝟙 U) (torusInversion Sₖ)) ≫
      γ (SmoothSite.productMap (𝟙 U) uₖ) =
    γ (SmoothSite.productMap (𝟙 U) uₖ) ≫ γ (SmoothSite.productMap (𝟙 U) (torusInversion Sₖ))
  simp only [← Functor.map_comp, ← SmoothSite.productMap_comp, Category.id_comp, h₁, h₂]

private theorem torusDoubleInversion_comp_inner (X : Cor k) :
    torusDoubleInversion k X ≫ inner(X) = inner(X) ≫ torusDoubleInversion k X :=
  ((Cor.parameterProductMap (torusInversion Sₖ)).naturality (torusUnitProjector k X)).symm

/-- Outer inversion preserves both unit reductions. -/
theorem torusDoubleInversion_reduction (X : Cor k) :
    torusDoubleInversion k X ≫ torusDoubleReduction k X =
      torusDoubleReduction k X ≫ torusDoubleInversion k X := by
  rw [torusDoubleReduction, ← Category.assoc,
    complement_naturality k _ _ _ (torusDoubleInversion_comp_inner k X), Category.assoc,
    complement_naturality k _ _ _ (torusDoubleInversion_comp_outer k X), ← Category.assoc]

/-- On the actual product, inversion of the outer torus is involutive. -/
@[reassoc]
theorem torusDoubleInversion_comp_self (X : Cor k) :
    torusDoubleInversion k X ≫ torusDoubleInversion k X = 𝟙 _ := by
  let U := ((F).obj X).toSmoothSite
  change γ (SmoothSite.productMap (𝟙 U) (torusInversion Sₖ)) ≫
      γ (SmoothSite.productMap (𝟙 U) (torusInversion Sₖ)) = _
  rw [← Functor.map_comp, ← SmoothSite.productMap_comp, Category.id_comp,
    torusInversion_comp_self, SmoothSite.productMap_id, CategoryTheory.Functor.map_id]
  rfl

/-- Outer inversion commutes with the actual signed exterior extension. -/
@[reassoc]
theorem torusDoubleInversion_naturality {X Y : Cor k} (α : (F).obj X ⟶ (F).obj Y) :
    torusDoubleInversion k X ≫ torusOuterReducedExtension k α =
      torusOuterReducedExtension k α ≫ torusDoubleInversion k Y := by
  have h : torusDoubleInversion k X ≫ (F).map α = (F).map α ≫ torusDoubleInversion k Y :=
    ((Cor.parameterProductMap (torusInversion Sₖ)).naturality α).symm
  rw [torusOuterReducedExtension, ← Category.assoc, h, Category.assoc,
    complement_naturality k _ _ _ (torusDoubleInversion_comp_outer k Y), ← Category.assoc]

/-- The two occurrences of the same outer inversion cancel on every signed extension. -/
theorem torusDoubleInversion_conjugate {X Y : Cor k} (α : (F).obj X ⟶ (F).obj Y) :
    torusDoubleInversion k X ≫ torusOuterReducedExtension k α ≫ torusDoubleInversion k Y =
      torusOuterReducedExtension k α := by
  rw [← Category.assoc, torusDoubleInversion_naturality, Category.assoc,
    torusDoubleInversion_comp_self, Category.comp_id]

/-- The complementary unit projector is itself idempotent on the native torus product. -/
theorem torusUnitComplement_idempotent (X : Cor k) :
    (𝟙 _ - torusUnitProjector k X) ≫ (𝟙 _ - torusUnitProjector k X) =
      𝟙 _ - torusUnitProjector k X := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
    torusUnitProjector_idempotent]
  abel

/-- A source-reduced correspondence remains source reduced on both factors after extension. -/
@[reassoc]
theorem torusDoubleReduction_outerReducedExtension {X Y : Cor k}
    (α : (F).obj X ⟶ (F).obj Y) (hα : (𝟙 _ - torusUnitProjector k X) ≫ α = α) :
    torusDoubleReduction k X ≫ torusOuterReducedExtension k α =
      torusOuterReducedExtension k α := by
  have ho : (𝟙 _ - outer(X)) ≫ (F).map α = (F).map α ≫ (𝟙 _ - outer(Y)) :=
    (complement_naturality k _ _ _ (torusUnitProjector_naturality k α)).symm
  have hi : (𝟙 _ - inner(X)) ≫ (F).map α = (F).map α := by
    simpa only [Functor.map_comp, Functor.map_sub, CategoryTheory.Functor.map_id] using
      congrArg (F).map hα
  rw [torusDoubleReduction, torusOuterReducedExtension, Category.assoc, ← Category.assoc
    (𝟙 _ - outer(X)) ((F).map α), ho, Category.assoc ((F).map α),
    torusUnitComplement_idempotent, ← Category.assoc, hi]

/-- A target-reduced correspondence remains target reduced on both factors after extension. -/
@[reassoc]
theorem torusOuterReducedExtension_doubleReduction {X Y : Cor k}
    (α : (F).obj X ⟶ (F).obj Y) (hα : α ≫ (𝟙 _ - torusUnitProjector k Y) = α) :
    torusOuterReducedExtension k α ≫ torusDoubleReduction k Y =
      torusOuterReducedExtension k α := by
  have hi : (F).map α ≫ (𝟙 _ - inner(Y)) = (F).map α := by
    simpa only [Functor.map_comp, Functor.map_sub, CategoryTheory.Functor.map_id] using
      congrArg (F).map hα
  rw [torusDoubleReduction, torusOuterReducedExtension, Category.assoc,
    ← Category.assoc (𝟙 _ - outer(Y)), ← unitComplements_commute,
    Category.assoc (𝟙 _ - inner(Y)), torusUnitComplement_idempotent,
    ← Category.assoc ((F).map α), hi]

end AlgebraicGeometry.PresheafWithTransfers
