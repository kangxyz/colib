/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Colib.AlgebraicGeometry.Correspondences.Additive
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Support
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Retained
public import Colib.AlgebraicGeometry.Correspondences.Category
import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.Component
import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-!
# Prime correspondence of the retained parameter graph

The finite projection of the retained parameter graph reaches exactly the same
source component as the original prime support. Its generic point is therefore
an admissible point for native finite correspondences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

attribute [local instance] Stacks.Chow.isIntegral_integralComponentAt
attribute [local instance] Classical.propDecidable

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))
  (z : torusPowerCutAmbient k X Y)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "XG" => (product X Gₘ)
local notation "YG" => (product Y Gₘ)
local notation "V" => (torusPowerCutRetainedTarget k Y)
local notation "g" => torusPowerCutSource k X Y z
set_option quotPrecheck false in
local notation "Pₜ" => (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subscheme
set_option quotPrecheck false in
local notation "j" => (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subschemeι
set_option quotPrecheck false in
local notation "Aₚ" => Γ(Pₜ, ⊤)

/-- The actual retained graph for the prime support and its Laurent power parameter. -/
abbrev torusPowerCutRetainedPrimeMap (n : ℕ) (u₀ : Aₚˣ) :
    Pₜ ⟶ pullback (XG).hom (V).hom :=
  torusPowerCutRetainedParameterGraph k j (torusSupportCoordinate k g ^ n * u₀⁻¹)

/-- For all large exponents the retained graph is finite over the same source
component, and its generic point defines a native prime correspondence. -/
theorem exists_isFiniteCorrespondencePoint_torusPowerCutRetainedPrimeMap
    (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z) (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsFinite (torusPowerCutRetainedPrimeMap k X Y z n u₀ ≫ pullback.fst (XG).hom (V).hom) ∧
      Set.range (torusPowerCutRetainedPrimeMap k X Y z n u₀ ≫ pullback.fst (XG).hom (V).hom) =
        Set.range g ∧
      IsFiniteCorrespondencePoint (XG).hom (V).hom
        (torusPowerCutRetainedPrimeMap k X Y z n u₀ (genericPoint Pₜ)) := by
  let : IsFinite (j ≫ pullback.fst (XG).hom (YG).hom) := hz.1
  let : IsFinite g := hz.1
  obtain ⟨N, hN⟩ := exists_isFinite_torusPowerCutRetainedParameterGraph k j u₀
  refine ⟨N, fun n hn => ?_⟩
  let m := torusPowerCutRetainedPrimeMap k X Y z n u₀
  let mₓ := m ≫ pullback.fst (XG).hom (V).hom
  let a := torusSupportCoordinate k g ^ n * u₀⁻¹
  let : IsClosedImmersion m := torusPowerCutRetainedParameterGraph_isClosedImmersion k j a
  have hm : mₓ = torusPowerCutParameterProjection k g a :=
    torusPowerCutRetainedParameterGraph_fst k j a
  let : IsFinite mₓ := hN n hn
  have hb : g ≫ (productFst X Gₘ).left = mₓ ≫ (productFst X Gₘ).left :=
    ((congrArg (fun h => h ≫ (productFst X Gₘ).left) hm).trans
      (torusPowerCutParameterProjection_fst k g a)).symm
  let f : X.left ⟶ Sₖ := X.hom
  have hr : Set.range mₓ = Set.range g :=
    NativeTorusPolynomial.range_eq_of_finite_of_torus_component f g mₓ hz.2 hb
  have hcomp : Set.range mₓ ∈ irreducibleComponents (XG).left := hr.symm ▸ hz.2
  refine ⟨inferInstance, hr, ?_⟩
  apply isFiniteCorrespondencePoint_finiteMap (XG).hom (V).hom m (genericPoint Pₜ)
  · rw [Category.assoc]
    infer_instance
  · simp only [Category.assoc, finiteCyclePushforward_range_integralComponentAt,
      coe_support_integralComponentAt, genericPoint_closure, Set.image_univ]
    exact hcomp

/-- The retained prime graph with the given original integer weight. -/
def torusPowerCutRetainedPrime (n : ℕ) (u₀ : Aₚˣ) (r : ℤ)
    (h : IsFiniteCorrespondencePoint (XG).hom (V).hom
      (torusPowerCutRetainedPrimeMap k X Y z n u₀ (genericPoint Pₜ))) :
    Cor.mk XG ⟶ Cor.mk V :=
  singleFiniteCorrespondence (XG).hom (V).hom
    (torusPowerCutRetainedPrimeMap k X Y z n u₀ (genericPoint Pₜ)) h r

/-- The actual closed graph pushforward preserves the signed weight. -/
theorem torusPowerCutRetainedPrime_val (n : ℕ) (u₀ : Aₚˣ) (r : ℤ)
    (h : IsFiniteCorrespondencePoint (XG).hom (V).hom
      (torusPowerCutRetainedPrimeMap k X Y z n u₀ (genericPoint Pₜ))) :
    (torusPowerCutRetainedPrime k X Y z n u₀ r h).val =
      finiteCyclePushforward (torusPowerCutRetainedPrimeMap k X Y z n u₀)
        (Function.locallyFinsuppWithin.single (genericPoint Pₜ) r) := by
  exact (finiteCyclePushforward_single_of_isClosedImmersion
    (torusPowerCutRetainedPrimeMap k X Y z n u₀) (genericPoint Pₜ) r).symm

end AlgebraicGeometry.Cor
