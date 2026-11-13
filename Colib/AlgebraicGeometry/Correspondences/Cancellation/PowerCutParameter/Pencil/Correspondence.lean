/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Support
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.Retained
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor
import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.GenericImage
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-!
# The interpolated power-cut correspondence on a prime support

The extended prime support is integral and remains over the corresponding
source component after adding the affine-line parameter. The finite numerator
and denominator cuts therefore give a signed correspondence on the literal
product `X × A¹`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))
  (z : torusPowerCutAmbient k X Y)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "A₁" => (additiveGroupObject Sₖ)
local notation "XG" => (product X Gₘ)
local notation "YG" => (product Y Gₘ)
local notation "B" => (product X A₁)
local notation "V" => (torusPowerCutRetainedTarget k Y)
local notation "g" => torusPowerCutSource k X Y z
set_option quotPrecheck false in
local notation "Pₜ" => (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subscheme
set_option quotPrecheck false in
local notation "b" => (g ≫ (XG).hom)
set_option quotPrecheck false in
local notation "W" => pullback b (A₁).hom
set_option quotPrecheck false in
local notation "π" => pullback.fst b (A₁).hom
local notation "p" => torusPowerCutPencilProjection k g
set_option quotPrecheck false in
local notation "bW" => (π ≫ b)
set_option quotPrecheck false in
local notation "Z₀(" s ")" => AffineLineFiber.fiber (sectionToAffineLine bW s) (0 : k)
set_option quotPrecheck false in
local notation "i₀(" s ")" => AffineLineFiber.inclusion (sectionToAffineLine bW s) (0 : k)
set_option quotPrecheck false in
local notation "Aₚ" => Γ(Pₜ, ⊤)

/-- Both actual pencil cuts are nonzero and finite with generic images. -/
structure TorusPowerCutPencilAdmissibleAt (u₀ : Aₚˣ) (m n : ℕ) : Prop where
  numerator_nonzero : torusPowerCutPencilNumerator k g u₀ m n ≠ 0
  denominator_nonzero : torusPowerCutPencilDenominator k g u₀ m n ≠ 0
  numerator_finite : IsFinite (i₀(torusPowerCutPencilNumerator k g u₀ m n) ≫ p)
  denominator_finite : IsFinite (i₀(torusPowerCutPencilDenominator k g u₀ m n) ≫ p)
  numerator_generic : ∀ x : genericPoints Z₀(torusPowerCutPencilNumerator k g u₀ m n),
    (i₀(torusPowerCutPencilNumerator k g u₀ m n) ≫ p) x.val ∈ genericPoints (B).left
  denominator_generic : ∀ x : genericPoints Z₀(torusPowerCutPencilDenominator k g u₀ m n),
    (i₀(torusPowerCutPencilDenominator k g u₀ m n) ≫ p) x.val ∈ genericPoints (B).left

/-- A common lower bound makes both cuts of the entire pencil admissible. -/
theorem exists_torusPowerCutPencilAdmissibleAt
    (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z) (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → TorusPowerCutPencilAdmissibleAt k X Y z u₀ m n := by
  let : IsFinite g := hz.1
  let : IsIntegral Pₜ := isIntegral_integralComponentAt z
  let : IsLocallyNoetherian Pₜ := LocallyOfFiniteType.isLocallyNoetherian (Y := Sₖ) b
  let : IsIntegral W := inferInstanceAs (IsIntegral (pullback b (A₁).hom))
  let : IsNoetherian W := isNoetherian_of_finiteType_of_isNoetherian (Y := Sₖ) bW
  let F : (B).left ⟶ Sₖ := (B).hom
  let : Smooth F := inferInstanceAs (Smooth (B).hom)
  let G := supportParameterExtension g A₁
  let : IsFinite G := supportParameterExtension_isFinite g A₁
  have hrange := supportParameterExtension_range_mem_irreducibleComponents g A₁ hz.2
  have hgen := NativeTorusPolynomial.sectionCut_nonzero_and_generic_of_finite_torus_component
    F G hrange
  have hproj : p ≫ F = bW := torusPowerCutPencilProjection_over k g
  change (∀ s : Γ(W, ⊤), IsFinite
    (AffineLineFiber.inclusion (sectionToAffineLine (p ≫ F) s) 0 ≫ p) →
    s ≠ 0 ∧ ∀ x : genericPoints (AffineLineFiber.fiber (sectionToAffineLine (p ≫ F) s) 0),
      (AffineLineFiber.inclusion (sectionToAffineLine (p ≫ F) s) 0 ≫ p) x.val ∈
        genericPoints (B).left) at hgen
  rw [hproj] at hgen
  obtain ⟨N, hN⟩ := exists_isFinite_torusPowerCutPencil k g u₀
  refine ⟨N, fun m n hm hn => ?_⟩
  obtain ⟨ha, hb⟩ := hN m n hm hn
  obtain ⟨hanz, hag⟩ := hgen _ ha
  obtain ⟨hbnz, hbg⟩ := hgen _ hb
  exact ⟨hanz, hbnz, ha, hb, hag, hbg⟩

/-- The signed pencil correspondence with the two original torus coordinates retained. -/
def torusPowerCutPencilRetainedPrime (u₀ : Aₚˣ) (m n : ℕ)
    (h : TorusPowerCutPencilAdmissibleAt k X Y z u₀ m n) : Cor.mk B ⟶ Cor.mk V := by
  let j := (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subschemeι
  let r := torusPowerCutPencilRetainedSupportMap k j
  let q := r ≫ pullback.snd (B).hom (V).hom
  have hr : r ≫ pullback.fst (B).hom (V).hom = p :=
    torusPowerCutPencilRetainedSupportMap_fst k j
  have hq : p ≫ (B).hom = q ≫ (V).hom := by
    have hp := congrArg (· ≫ (B).hom) hr.symm
    have he := congrArg (r ≫ ·) (pullback.condition (f := (B).hom) («g» := (V).hom))
    exact hp.trans ((Category.assoc _ _ _).trans (he.trans (Category.assoc _ _ _).symm))
  let : IsFinite (AffineLineFiber.inclusion (sectionToAffineLine
      (p ≫ (B).hom) (torusPowerCutPencilNumerator k g u₀ m n)) 0 ≫ p) := by
    rw [torusPowerCutPencilProjection_over]
    exact h.numerator_finite
  let : IsFinite (AffineLineFiber.inclusion (sectionToAffineLine
      (p ≫ (B).hom) (torusPowerCutPencilDenominator k g u₀ m n)) 0 ≫ p) := by
    rw [torusPowerCutPencilProjection_over]
    exact h.denominator_finite
  refine signedSectionCutCorrespondence p q hq (torusPowerCutPencilNumerator k g u₀ m n)
    (torusPowerCutPencilDenominator k g u₀ m n) ?_ ?_
  · rw [torusPowerCutPencilProjection_over]
    exact h.numerator_generic
  · rw [torusPowerCutPencilProjection_over]
    exact h.denominator_generic

/-- Project the signed pencil correspondence to the original target scheme. -/
def torusPowerCutPencilPrime (u₀ : Aₚˣ) (m n : ℕ)
    (h : TorusPowerCutPencilAdmissibleAt k X Y z u₀ m n) : Cor.mk B ⟶ Cor.mk Y :=
  torusPowerCutPencilRetainedPrime k X Y z u₀ m n h ≫
    (graphFunctor k).map (productFst YG Gₘ ≫ productFst Y Gₘ)

end AlgebraicGeometry.Cor
