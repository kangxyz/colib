/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RetainedPowerCutSupport
public import Colib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
public import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph

/-!
# The closed parameter graph retaining the original torus coordinates

The original support in `(X × Gₘ,t) × (Y × Gₘ,v)` is embedded as the graph
of the parameter in `(X × Gₘ,λ) × ((Y × Gₘ,v) × Gₘ,t)`. Its maps to the
new source and the retained target are the specified original maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]
  {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (j : P ⟶ pullback
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Y (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "Gₓ" => (product X Gₘ)
local notation "Gᵧ" => (product Y Gₘ)
local notation "V" => (torusPowerCutRetainedTarget k Y)
local notation "B" => (product X V)
set_option quotPrecheck false in
local notation "τ" => (multiplicativeGroupBaseChange Sₖ ↘ Sₖ)

set_option quotPrecheck false in
local notation "g" => (j ≫ pullback.fst (Gₓ).hom (Gᵧ).hom)
set_option quotPrecheck false in
local notation "r" => (j ≫ (torusPowerCutAmbientSchemeIso k X Y).hom)
set_option quotPrecheck false in
local notation "b" => (r ≫ (B).hom)
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)

/-- The actual graph in the product with the retained target. -/
def torusPowerCutRetainedParameterGraph (a : Aₚˣ) : P ⟶ pullback (Gₓ).hom (V).hom :=
  torusParameterGraph b a ≫ pullbackParameterExtensionMap r (B).hom (Gₘ).hom ≫
    (productSwapLast X V Gₘ).left

private theorem retained_base_projection :
    r ≫ (productFst X V).left = torusSupportBaseProjection k g := by
  have h := congrArg (fun q => q.left) (torusPowerCutAmbientIso_hom_source k X Y)
  change (torusPowerCutAmbientIso k X Y).hom.left ≫ (productFst X V).left =
    (productFst Gₓ Gᵧ).left ≫ (productFst X Gₘ).left at h
  change (j ≫ (torusPowerCutAmbientIso k X Y).hom.left) ≫ (productFst X V).left = _
  rw [Category.assoc, h]
  exact (Category.assoc _ _ _).symm

private theorem retained_structureMap : b = g ≫ (Gₓ).hom := by
  change (j ≫ (torusPowerCutAmbientIso k X Y).hom.left) ≫ (B).hom = _
  rw [Category.assoc, MorphismProperty.Over.w]
  exact (Category.assoc _ _ _).symm

@[reassoc] private theorem extension_fst :
    pullbackParameterExtensionMap r (B).hom (Gₘ).hom ≫ (productFst B Gₘ).left =
      pullback.fst b τ ≫ r :=
  pullbackParameterExtensionMap_fst r (B).hom (Gₘ).hom

private theorem extension_snd :
    pullbackParameterExtensionMap r (B).hom (Gₘ).hom ≫ (productSnd B Gₘ).left =
      pullback.snd b τ :=
  pullbackParameterExtensionMap_snd r (B).hom (Gₘ).hom

/-- The first projection of the closed graph is its projection to the new source. -/
@[reassoc] theorem torusPowerCutRetainedParameterGraph_fst (a : Aₚˣ) :
    torusPowerCutRetainedParameterGraph k j a ≫ pullback.fst (Gₓ).hom (V).hom =
      torusPowerCutParameterProjection k g a := by
  apply pullback.hom_ext
  · have h : productSwapLast X V Gₘ ≫ productFst Gₓ V ≫ productFst X Gₘ =
        productFst B Gₘ ≫ productFst X V := by simp [productSwapLast]
    have h' := congrArg (fun q => q.left) h
    change (productSwapLast X V Gₘ).left ≫ (productFst Gₓ V).left ≫
      (productFst X Gₘ).left = (productFst B Gₘ).left ≫ (productFst X V).left at h'
    change (torusPowerCutRetainedParameterGraph k j a ≫ (productFst Gₓ V).left) ≫
      (productFst X Gₘ).left = torusPowerCutParameterProjection k g a ≫
        (productFst X Gₘ).left
    simp only [torusPowerCutRetainedParameterGraph, Category.assoc, h', extension_fst_assoc,
      torusParameterGraph_fst_assoc, torusPowerCutParameterProjection_fst]
    exact retained_base_projection k j
  · have h : productSwapLast X V Gₘ ≫ productFst Gₓ V ≫ productSnd X Gₘ =
        productSnd B Gₘ := by simp [productSwapLast]
    have h' := congrArg (fun q => q.left) h
    change (productSwapLast X V Gₘ).left ≫ (productFst Gₓ V).left ≫
      (productSnd X Gₘ).left = (productSnd B Gₘ).left at h'
    change (torusPowerCutRetainedParameterGraph k j a ≫ (productFst Gₓ V).left) ≫
      (productSnd X Gₘ).left = torusPowerCutParameterProjection k g a ≫
        (productSnd X Gₘ).left
    simp only [torusPowerCutRetainedParameterGraph, Category.assoc, h', extension_snd,
      torusParameterGraph_snd, torusPowerCutParameterProjection_snd]
    let parameterMap (f : P ⟶ Sₖ) : P ⟶ multiplicativeGroupBaseChange Sₖ :=
      (nativeTorusPoint f a).left
    exact congrArg parameterMap (retained_structureMap k j)

/-- The second projection is the original map to the retained target. -/
@[reassoc] theorem torusPowerCutRetainedParameterGraph_snd (a : Aₚˣ) :
    torusPowerCutRetainedParameterGraph k j a ≫ pullback.snd (Gₓ).hom (V).hom =
      r ≫ pullback.snd X.hom (V).hom := by
  have h := congrArg (fun q => q.left) (productSwapLast_snd X V Gₘ)
  change (productSwapLast X V Gₘ).left ≫ (productSnd Gₓ V).left =
    (productFst B Gₘ).left ≫ (productSnd X V).left at h
  change torusPowerCutRetainedParameterGraph k j a ≫ (productSnd Gₓ V).left =
    r ≫ (productSnd X V).left
  simp only [torusPowerCutRetainedParameterGraph, Category.assoc, h, extension_fst_assoc,
    torusParameterGraph_fst_assoc]

instance torusPowerCutRetainedParameterGraph_isClosedImmersion [IsClosedImmersion j] (a : Aₚˣ) :
    IsClosedImmersion (torusPowerCutRetainedParameterGraph k j a) := by
  let : IsClosedImmersion r := inferInstance
  let : IsClosedImmersion (pullbackParameterExtensionMap r (B).hom (Gₘ).hom) :=
    MorphismProperty.of_isPullback
      (pullbackParameterExtension_isPullback r (B).hom (Gₘ).hom).flip inferInstance
  let e := (forgetScheme Sₖ).mapIso (productSwapLastIso X V Gₘ)
  let : IsIso (productSwapLast X V Gₘ).left := inferInstanceAs (IsIso e.hom)
  unfold torusPowerCutRetainedParameterGraph
  infer_instance

/-- The closed graph of the power parameter is finite over its original new
source projection for all sufficiently large exponents. -/
theorem exists_isFinite_torusPowerCutRetainedParameterGraph [IsFinite g] (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsFinite (torusPowerCutRetainedParameterGraph k j (torusSupportCoordinate k g ^ n * u₀⁻¹) ≫
        pullback.fst (Gₓ).hom (V).hom) := by
  simpa only [torusPowerCutRetainedParameterGraph_fst] using
    exists_isFinite_torusPowerCutParameterProjection k g u₀

end AlgebraicGeometry.Cor
