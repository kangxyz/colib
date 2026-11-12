/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.QuasiCompact
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ParameterGraph
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut
import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph

/-!
# Finiteness over the retained Laurent parameter

After adding a torus parameter `λ`, the equations `t ^ n - λ` and
`t ^ n - λ * u` are finite cuts over `X × Gₘ,λ` for large `n`. Their actual
zero-scheme projections are the projections of the graphs of the units
`t ^ n` and `t ^ n * u⁻¹`, with the original source projection retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k] {X : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (g : P ⟶ (SmoothSite.product X
    (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).left)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "T" => (product X Gₘ)
local notation "D" => (product T Gₘ)

set_option quotPrecheck false in
local notation "b" => (g ≫ (T).hom)
local notation "W" => torusParameterScheme b
set_option quotPrecheck false in
local notation "τ" => (multiplicativeGroupBaseChange Sₖ ↘ Sₖ)
set_option quotPrecheck false in
local notation "π" => pullback.fst b τ
set_option quotPrecheck false in
local notation "λMap" => pullback.snd b τ
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)

/-- The graph's projection to the new source retains the original base map and
uses the specified unit as the new torus parameter. -/
def torusPowerCutParameterProjection (a : Aₚˣ) : P ⟶ (T).left :=
  pullback.lift (torusSupportBaseProjection k g) (nativeTorusPoint b a).left (by
    change torusSupportBaseProjection k g ≫ X.hom = (nativeTorusPoint b a).left ≫
      (multiplicativeGroupBaseChange Sₖ ↘ Sₖ)
    exact (Category.assoc g (productFst X Gₘ).left X.hom).trans
      (nativeTorusPoint_over b a).symm)

/-- The projection to the old source base is the actual original map. -/
@[reassoc (attr := simp)] theorem torusPowerCutParameterProjection_fst (a : Aₚˣ) :
    torusPowerCutParameterProjection k g a ≫ (productFst X Gₘ).left =
      torusSupportBaseProjection k g :=
  pullback.lift_fst _ _ _

/-- The new source torus map is the native point of the chosen unit. -/
@[reassoc (attr := simp)] theorem torusPowerCutParameterProjection_snd (a : Aₚˣ) :
    torusPowerCutParameterProjection k g a ≫ (productSnd X Gₘ).left =
      (nativeTorusPoint b a).left :=
  pullback.lift_snd _ _ _

private abbrev sourceDoubleMap : W ⟶ (D).left :=
  pullbackParameterExtensionMap g (T).hom (Gₘ).hom

@[reassoc] private theorem sourceDoubleMap_fst :
    sourceDoubleMap k g ≫ (productFst T Gₘ).left = π ≫ g :=
  pullbackParameterExtensionMap_fst g (T).hom (Gₘ).hom

private theorem sourceDoubleMap_snd :
    sourceDoubleMap k g ≫ (productSnd T Gₘ).left = λMap :=
  pullbackParameterExtensionMap_snd g (T).hom (Gₘ).hom

private def sourceParameterMap : W ⟶ (D).left :=
  sourceDoubleMap k g ≫ (productSwapLast X Gₘ Gₘ).left

private theorem sourceParameterMap_isFinite [IsFinite g] : IsFinite (sourceParameterMap k g) := by
  let e := (forgetScheme Sₖ).mapIso (productSwapLastIso X Gₘ Gₘ)
  let : IsIso (productSwapLast X Gₘ Gₘ).left := inferInstanceAs (IsIso e.hom)
  let : IsFinite (sourceDoubleMap k g) := MorphismProperty.of_isPullback
    (pullbackParameterExtension_isPullback g (T).hom (Gₘ).hom).flip inferInstance
  unfold sourceParameterMap
  infer_instance

private abbrev sourceParameterProjection : W ⟶ (T).left :=
  sourceParameterMap k g ≫ (productFst T Gₘ).left

private theorem sourceParameterMap_fst_fst :
    (sourceParameterProjection k g) ≫ (productFst X Gₘ).left = π ≫ g ≫ (productFst X Gₘ).left := by
  have h : productSwapLast X Gₘ Gₘ ≫ productFst T Gₘ ≫ productFst X Gₘ =
      productFst T Gₘ ≫ productFst X Gₘ := by simp [productSwapLast]
  have h' := congrArg (fun φ => φ.left) h
  change (productSwapLast X Gₘ Gₘ).left ≫ (productFst T Gₘ).left ≫
    (productFst X Gₘ).left = (productFst T Gₘ).left ≫ (productFst X Gₘ).left at h'
  simp only [sourceParameterProjection, sourceParameterMap, Category.assoc, h',
    sourceDoubleMap_fst_assoc]

private theorem sourceParameterMap_fst_snd :
    sourceParameterProjection k g ≫ (productSnd X Gₘ).left = λMap := by
  have h : productSwapLast X Gₘ Gₘ ≫ productFst T Gₘ ≫ productSnd X Gₘ =
      productSnd T Gₘ := by simp [productSwapLast]
  have h' := congrArg (fun φ => φ.left) h
  change (productSwapLast X Gₘ Gₘ).left ≫ (productFst T Gₘ).left ≫
    (productSnd X Gₘ).left = (productSnd T Gₘ).left at h'
  simp only [sourceParameterProjection, sourceParameterMap, Category.assoc, h',
    sourceDoubleMap_snd]

private theorem sourceParameterMap_snd :
    sourceParameterMap k g ≫ (productSnd T Gₘ).left = π ≫ g ≫ (productSnd X Gₘ).left := by
  have h' := congrArg (fun φ => φ.left) (productSwapLast_snd X Gₘ Gₘ)
  change (productSwapLast X Gₘ Gₘ).left ≫ (productSnd T Gₘ).left =
    (productFst T Gₘ).left ≫ (productSnd X Gₘ).left at h'
  simp only [sourceParameterMap, Category.assoc, h', sourceDoubleMap_fst_assoc]

private theorem torusParameterGraph_comp_projection (a : Aₚˣ) :
    torusParameterGraph b a ≫ sourceParameterProjection k g =
      torusPowerCutParameterProjection k g a := by
  apply pullback.hom_ext
  · change (torusParameterGraph b a ≫ (sourceParameterProjection k g)) ≫ (productFst X Gₘ).left = _
    rw [Category.assoc, sourceParameterMap_fst_fst, torusParameterGraph_fst_assoc]
    exact (torusPowerCutParameterProjection_fst k g a).symm
  · change (torusParameterGraph b a ≫ (sourceParameterProjection k g)) ≫ (productSnd X Gₘ).left = _
    rw [Category.assoc, sourceParameterMap_fst_snd, torusParameterGraph_snd]
    exact (torusPowerCutParameterProjection_snd k g a).symm

/-- For all large exponents, the graph of `t ^ n * u⁻¹` is finite over the
new source `X × Gₘ`. Taking `u = 1` gives the graph of `t ^ n`. -/
theorem exists_isFinite_torusPowerCutParameterProjection [IsFinite g] (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsFinite (torusPowerCutParameterProjection k g
      (torusSupportCoordinate k g ^ n * u₀⁻¹)) := by
  let f : (T).left ⟶ Sₖ := (T).hom
  let : QuasiCompact f := inferInstanceAs (QuasiCompact (T).hom)
  let : CompactSpace (T).left := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsFinite (sourceParameterMap k g) := sourceParameterMap_isFinite k g
  let uW := torusParameterCoordinate b * Units.map (π).appTop.hom.toMonoidHom u₀
  let tW := (sourceParameterMap k g ≫ (productSnd T Gₘ).left).appTop
    (multiplicativeGroupBaseChangeCoordinate Sₖ).val
  have ht : tW = (π).appTop (torusSupportCoordinate k g).val := by
    change (sourceParameterMap k g ≫ (productSnd T Gₘ).left).appTop _ =
      (π).appTop ((g ≫ (productSnd X Gₘ).left).appTop _)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sourceParameterMap_snd]
  have hb : (sourceParameterProjection k g) ≫ (T).hom = π ≫ b := by
    change (sourceParameterProjection k g) ≫ (productFst X Gₘ).left ≫ X.hom =
      π ≫ g ≫ (productFst X Gₘ).left ≫ X.hom
    rw [← Category.assoc (sourceParameterProjection k g) (productFst X Gₘ).left X.hom,
      sourceParameterMap_fst_fst, Category.assoc, Category.assoc]
  obtain ⟨N, hN⟩ := NativeTorusPolynomial.exists_isFinite_power_sub_unit_of_compactSpace
    f (sourceParameterMap k g) uW
  refine ⟨N, fun n hn => ?_⟩
  let a := torusSupportCoordinate k g ^ n
  have hs : torusParameterEquation b a u₀ = tW ^ n - uW.val := by
    change (π).appTop ((torusSupportCoordinate k g).val ^ n) -
      (torusParameterCoordinate b).val * (π).appTop u₀.val = tW ^ n - _
    rw [ht, map_pow]
    rfl
  have hf : torusParameterZeroMap b a u₀ =
      sectionToAffineLine (sourceParameterProjection k g ≫ (T).hom) (tW ^ n - uW.val) := by
    change sectionToAffineLine (π ≫ b) (torusParameterEquation b a u₀) = _
    rw [hb, hs]
  let i := AffineLineFiber.inclusion (torusParameterZeroMap b a u₀) 0
  have hi : IsFinite (i ≫ (sourceParameterProjection k g)) := by
    change IsFinite (AffineLineFiber.inclusion (torusParameterZeroMap b a u₀) 0 ≫
      sourceParameterProjection k g)
    rw [hf]
    exact hN n hn
  let e := torusParameterGraphZeroIso b a u₀
  have hfin : IsFinite (e.hom ≫ i ≫ (sourceParameterProjection k g)) := inferInstance
  rw [← Category.assoc, torusParameterGraphZeroIso_hom_inclusion,
    torusParameterGraph_comp_projection] at hfin
  exact hfin

end AlgebraicGeometry.Cor
