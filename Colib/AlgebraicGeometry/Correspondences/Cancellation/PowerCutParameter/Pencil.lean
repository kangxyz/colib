/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Product
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.QuasiCompact
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ParameterSupport
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut

/-!
# The finite pencil of two Laurent power cuts

The affine-line parameter is the actual coordinate on the new source.
The interpolated numerator and the product denominator define finite whole
zero schemes over that source for all sufficiently large exponents.

At the unit endpoint the shared denominator factor is the second denominator.
At the zero endpoint it is the first. See Voevodsky, *Cancellation theorem*,
Remark 4.2.
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
local notation "A₁" => (additiveGroupObject Sₖ)
local notation "Gₘ" => (multiplicativeGroupObject Sₖ)
local notation "T" => (product X Gₘ)
local notation "B" => (product X A₁)
set_option quotPrecheck false in
local notation "b" => (g ≫ (T).hom)
set_option quotPrecheck false in
local notation "W" => (pullback b (A₁).hom)
set_option quotPrecheck false in
local notation "π" => pullback.fst b (A₁).hom
set_option quotPrecheck false in
local notation "e" => pullback.snd b (A₁).hom
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)

/-- The actual map to the source with the affine-line parameter. -/
def torusPowerCutPencilProjection : W ⟶ (B).left :=
  supportParameterExtension g A₁ ≫ (productFst B Gₘ).left

/-- The pencil projection preserves the original map to the coefficient field. -/
@[reassoc] theorem torusPowerCutPencilProjection_over :
    torusPowerCutPencilProjection k g ≫ (B).hom = π ≫ b := by
  rw [torusPowerCutPencilProjection, Category.assoc]
  exact supportParameterExtension_over g A₁

/-- The cleared numerator of the actual interpolation, with both exponents retained. -/
def torusPowerCutPencilNumerator (u₀ : Aₚˣ) (m n : ℕ) : Γ(W, ⊤) :=
  let t := (π).appTop (torusSupportCoordinate k g).val
  let u := (π).appTop u₀.val
  let s := (e).appTop (additiveGroupBaseChangeCoordinate Sₖ)
  s * (t ^ m - 1) * (t ^ n - u) + (1 - s) * (t ^ n - 1) * (t ^ m - u)

/-- The product of the two actual Laurent denominators. -/
def torusPowerCutPencilDenominator (u₀ : Aₚˣ) (m n : ℕ) : Γ(W, ⊤) :=
  let t := (π).appTop (torusSupportCoordinate k g).val
  let u := (π).appTop u₀.val
  (t ^ m - u) * (t ^ n - u)

set_option maxHeartbeats 800000 in
-- The actual native product and section maps need repeated definitional comparisons.
/-- Both whole zero schemes in the pencil are finite over `X × A¹` for a
common lower bound on the two exponents. -/
theorem exists_isFinite_torusPowerCutPencil [IsFinite g] (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      IsFinite (AffineLineFiber.inclusion (sectionToAffineLine (π ≫ b)
        (torusPowerCutPencilNumerator k g u₀ m n)) 0 ≫ torusPowerCutPencilProjection k g) ∧
      IsFinite (AffineLineFiber.inclusion (sectionToAffineLine (π ≫ b)
        (torusPowerCutPencilDenominator k g u₀ m n)) 0 ≫ torusPowerCutPencilProjection k g) := by
  let f : (B).left ⟶ Sₖ := (B).hom
  let : QuasiCompact f := inferInstanceAs (QuasiCompact (B).hom)
  let : CompactSpace (B).left := QuasiCompact.compactSpace_of_compactSpace (Y := Sₖ) f
  let q := multiplicativeGroupBaseChange Sₖ ↘ Sₖ
  let G : W ⟶ pullback f q := supportParameterExtension g A₁
  let p := torusPowerCutPencilProjection k g
  let u := Units.map (π).appTop.hom.toMonoidHom u₀
  let t := (π).appTop (torusSupportCoordinate k g).val
  let s := (productSnd X A₁).left.appTop (additiveGroupBaseChangeCoordinate Sₖ)
  let : IsFinite G := supportParameterExtension_isFinite g A₁
  let : IsAffineHom q := by
    let qℤ := multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))
    let : IsAffineHom qℤ := by
      change IsAffineHom (Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.C : ULift.{u} ℤ →+* LaurentPolynomial (ULift.{u} ℤ))))
      infer_instance
    change IsAffineHom (pullback.snd qℤ (specULiftZIsTerminal.from Sₖ))
    infer_instance
  let : IsAffineHom (pullback.fst f q) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) f q inferInstance
  let : IsAffineHom p := by
    change IsAffineHom (G ≫ pullback.fst f q)
    exact MorphismProperty.comp_mem @IsAffineHom _ _ inferInstance inferInstance
  let : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (Gₘ).hom)
  let : LocallyOfFiniteType (pullback.fst f q) :=
    MorphismProperty.pullback_fst (P := @LocallyOfFiniteType) f q inferInstance
  let : LocallyOfFiniteType p := by
    change LocallyOfFiniteType (G ≫ pullback.fst f q)
    exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ inferInstance inferInstance
  let tG := (G ≫ pullback.snd f q).appTop (multiplicativeGroupBaseChangeCoordinate Sₖ).val
  have ht : tG = t := by
    change (G ≫ (productSnd B Gₘ).left).appTop _ =
      (π).appTop ((g ≫ (productSnd X Gₘ).left).appTop _)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show G ≫ (productSnd B Gₘ).left = π ≫ g ≫ (productSnd X Gₘ).left from
        supportParameterExtension_oldFactor g A₁]
  have hs : p.appTop s = (e).appTop (additiveGroupBaseChangeCoordinate Sₖ) := by
    dsimp only [s]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show p ≫ (productSnd X A₁).left = e from by
        simpa only [p, torusPowerCutPencilProjection, Category.assoc] using
          supportParameterExtension_parameter g A₁]
    rfl
  have hb : p ≫ f = π ≫ b := torusPowerCutPencilProjection_over k g
  obtain ⟨N₁, h₁⟩ := NativeTorusPolynomial.exists_isFinite_power_cut_family_of_compactSpace f G u
  obtain ⟨N₂, h₂⟩ := NativeTorusPolynomial.exists_isFinite_power_sub_unit_of_compactSpace f G u
  refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
  have hnum := h₁ m n ((le_max_left _ _).trans hm) ((le_max_left _ _).trans hn) s
  change IsFinite (AffineLineFiber.inclusion (sectionToAffineLine (p ≫ f)
    (p.appTop s * (tG ^ m - 1) * (tG ^ n - u.val) +
      (1 - p.appTop s) * (tG ^ n - 1) * (tG ^ m - u.val))) 0 ≫ p) at hnum
  rw [hb, hs, ht] at hnum
  have hden (d : ℕ) (hd : N₂ ≤ d) :
      IsFinite (AffineLineFiber.inclusion (sectionToAffineLine (π ≫ b) (t ^ d - u.val)) 0 ≫ p) := by
    have h := h₂ d hd
    change IsFinite (AffineLineFiber.inclusion (sectionToAffineLine (p ≫ f)
      (tG ^ d - u.val)) 0 ≫ p) at h
    rwa [hb, ht] at h
  let : IsFinite (AffineLineFiber.inclusion (sectionToAffineLine (π ≫ b) (t ^ m - u.val)) 0 ≫ p) :=
    hden m ((le_max_right _ _).trans hm)
  let : IsFinite (AffineLineFiber.inclusion (sectionToAffineLine (π ≫ b) (t ^ n - u.val)) 0 ≫ p) :=
    hden n ((le_max_right _ _).trans hn)
  exact ⟨hnum, isFinite_sectionZero_mul (π ≫ b) p (t ^ m - u.val) (t ^ n - u.val)⟩

end AlgebraicGeometry.Cor
