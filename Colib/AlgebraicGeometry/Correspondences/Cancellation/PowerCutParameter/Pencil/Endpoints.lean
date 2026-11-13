/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.BaseChange
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.PolynomialParameter

/-!
# Restriction of the pencil equations to the actual endpoints

Restrict the original Laurent units and the external additive coordinate by the
actual section of the support product. The numerator at each endpoint retains
the other denominator factor, and the denominator is the same product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite AffineLineFiber

variable (k : Type u) [Field k] {X : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (g : P ⟶ (SmoothSite.product X
    (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).left)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "A₁" => additiveGroupObject Sₖ
set_option quotPrecheck false in
local notation "b" => (g ≫ (product X Gₘ).hom)
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)
set_option quotPrecheck false in
local notation "t" => (torusSupportCoordinate k g).val

private theorem restrict_fst (a : k) (r : Γ(P, ⊤)) :
    (nativeAdditiveParameterSection b a).appTop ((pullback.fst b (A₁).hom).appTop r) = r :=
  nativeAdditiveParameterSection_appTop_fst b a r

private theorem restrict_coordinate (a : k) :
    (nativeAdditiveParameterSection b a).appTop ((pullback.snd b (A₁).hom).appTop
      (additiveGroupBaseChangeCoordinate Sₖ)) = (b).appTop ((ΓSpecIso (.of k)).inv a) :=
  nativeAdditiveParameterSection_appTop_coordinate b a

/-- The actual numerator restricts by evaluation of the external parameter. -/
theorem torusPowerCutPencilNumerator_at (u₀ : Aₚˣ) (m n : ℕ) (a : k) :
    (nativeAdditiveParameterSection b a).appTop (torusPowerCutPencilNumerator k g u₀ m n) =
      (b).appTop ((ΓSpecIso (.of k)).inv a) * (t ^ m - 1) * (t ^ n - u₀.val) +
        (1 - (b).appTop ((ΓSpecIso (.of k)).inv a)) * (t ^ n - 1) * (t ^ m - u₀.val) := by
  simp only [torusPowerCutPencilNumerator, map_add, map_mul, map_sub, map_pow, map_one,
    restrict_coordinate, restrict_fst]

/-- The zero endpoint has the second numerator times the first denominator. -/
theorem torusPowerCutPencilNumerator_at_zero (u₀ : Aₚˣ) (m n : ℕ) :
    (nativeAdditiveParameterSection b 0).appTop (torusPowerCutPencilNumerator k g u₀ m n) =
      (t ^ n - 1) * (t ^ m - u₀.val) := by
  rw [torusPowerCutPencilNumerator_at]
  simp

/-- The unit endpoint has the first numerator times the second denominator. -/
theorem torusPowerCutPencilNumerator_at_one (u₀ : Aₚˣ) (m n : ℕ) :
    (nativeAdditiveParameterSection b 1).appTop (torusPowerCutPencilNumerator k g u₀ m n) =
      (t ^ m - 1) * (t ^ n - u₀.val) := by
  rw [torusPowerCutPencilNumerator_at]
  simp

/-- The denominator is the same product at both endpoints. -/
theorem torusPowerCutPencilDenominator_at (u₀ : Aₚˣ) (m n : ℕ) (a : k) :
    (nativeAdditiveParameterSection b a).appTop (torusPowerCutPencilDenominator k g u₀ m n) =
      (t ^ m - u₀.val) * (t ^ n - u₀.val) := by
  simp only [torusPowerCutPencilDenominator, map_mul, map_sub, map_pow, restrict_fst]

/-- Restriction along the actual affine parameter section recovers the original
support over the original source base. -/
theorem isPullback_torusPowerCutPencilProjection_at (a : k) :
    IsPullback (nativeAdditiveParameterSection b a) (torusSupportBaseProjection k g)
      (torusPowerCutPencilProjection k g) (nativeAdditiveParameterSection X.hom a) := by
  let f : X.left ⟶ Sₖ := X.hom
  let q := additiveGroupBaseChange Sₖ ↘ Sₖ
  let U := additiveGroupObject Sₖ
  let p := torusSupportBaseProjection k g
  let π := pullback.fst b q
  let pA := torusPowerCutPencilProjection k g
  let i := nativeAdditiveParameterSection b a
  let j := nativeAdditiveParameterSection f a
  have hb : p ≫ f = b := Category.assoc _ _ _
  have h₁ : pA ≫ pullback.fst f q = π ≫ p := by
    change (supportParameterExtension g U ≫ (productFst (product X U) Gₘ).left) ≫
      (productFst X U).left = π ≫ p
    rw [Category.assoc]
    exact supportParameterExtension_base g U
  have h₂ : pA ≫ nativeAdditivePolynomialParameter f = nativeAdditivePolynomialParameter b := by
    change (supportParameterExtension g U ≫ (productFst (product X U) Gₘ).left) ≫
      (productSnd X U).left ≫ (nativePolynomialAffineLineIso (.of k)).hom =
        pullback.snd b U.hom ≫ (nativePolynomialAffineLineIso (.of k)).hom
    rw [Category.assoc]
    exact supportParameterExtension_parameter_assoc g U _
  have hcomm : i ≫ pA = p ≫ j := by
    apply (nativeAdditivePolynomialParameter_isPullback f).hom_ext
    · have hi : i ≫ nativeAdditivePolynomialParameter b = b ≫ point a :=
        nativeAdditiveParameterSection_polynomialParameter b a
      have hj : j ≫ nativeAdditivePolynomialParameter f = f ≫ point a :=
        nativeAdditiveParameterSection_polynomialParameter f a
      calc
        _ = i ≫ nativeAdditivePolynomialParameter b := by rw [Category.assoc, h₂]
        _ = b ≫ point a := hi
        _ = p ≫ f ≫ point a :=
          (congrArg (· ≫ point a) hb.symm).trans (Category.assoc _ _ _)
        _ = p ≫ j ≫ nativeAdditivePolynomialParameter f := congrArg (p ≫ ·) hj.symm
        _ = _ := (Category.assoc _ _ _).symm
    · have hi : i ≫ π = 𝟙 P := nativeAdditiveParameterSection_fst b a
      have hj : j ≫ pullback.fst f q = 𝟙 X.left := nativeAdditiveParameterSection_fst f a
      change (i ≫ pA) ≫ pullback.fst f q = (p ≫ j) ≫ pullback.fst f q
      calc
        _ = (i ≫ π) ≫ p := by rw [Category.assoc, h₁, Category.assoc]
        _ = p := by rw [hi, Category.id_comp]
        _ = _ := by rw [Category.assoc, hj, Category.comp_id]
  have hOuter : IsPullback i (p ≫ f) (pA ≫ nativeAdditivePolynomialParameter f) (point a) := by
    rw [hb, h₂]
    exact nativeAdditiveParameterSection_isPullback b a
  exact hOuter.of_bot hcomm (nativeAdditiveParameterSection_isPullback f a)

set_option quotPrecheck false in
local notation "τ" => (additiveGroupBaseChange Sₖ ↘ Sₖ)
local notation "W" => pullback b τ
local notation "bW" => pullback.fst b τ ≫ b

/-- The entire endpoint zero scheme of a pencil equation is its actual
scheme-theoretic restriction to the original support. -/
theorem isPullback_torusPowerCutPencilZeroAt (a : k) (s : Γ(W, ⊤)) :
    IsPullback (sectionZeroBaseChangeMap bW (nativeAdditiveParameterSection b a) s)
      (AffineLineFiber.inclusion (sectionToAffineLine (nativeAdditiveParameterSection b a ≫ bW)
        ((nativeAdditiveParameterSection b a).appTop s)) 0 ≫ torusSupportBaseProjection k g)
      (AffineLineFiber.inclusion (sectionToAffineLine bW s) 0 ≫ torusPowerCutPencilProjection k g)
      (nativeAdditiveParameterSection X.hom a) :=
  (isPullback_sectionZeroBaseChangeMap bW (nativeAdditiveParameterSection b a) s).paste_vert
    (isPullback_torusPowerCutPencilProjection_at k g a)

end AlgebraicGeometry.Cor
