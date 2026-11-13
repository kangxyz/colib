/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Weighted
public import Colib.AlgebraicGeometry.GroupScheme.UnitPoints
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-!
# Power cuts with constant unit target

On a support whose target torus coordinate factors through the original unit
section, the numerator and denominator have the same global equation and
give identical whole zero fibers. Their signed correspondence vanishes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "tₖ" => multiplicativeGroupBaseChangeCoordinate Sₖ

/-- The actual coordinate on a target factoring through the unit is the global unit one. -/
theorem torusSupportCoordinate_eq_one_of_factor_unit {Y : SmoothSite Sₖ} {P : Scheme.{u}}
    (g : P ⟶ Y.left) (q : P ⟶ (SmoothSite.product Y Gₖ).left)
    (h : q = g ≫ (SmoothSite.Contraction.unitSection.app Y).left) :
    torusSupportCoordinate k (X := Y) (P := P) q = 1 := by
  have hu : (SmoothSite.torusOne Sₖ).left.appTop (tₖ).val = 1 := by
    have hpoint := nativeTorusPoint_coordinate (𝟙 Sₖ) (1 : (Γ(Sₖ, ⊤))ˣ)
    exact congrArg Units.val hpoint
  have hs : (SmoothSite.Contraction.unitSection.app Y).left ≫ pullback.snd Y.hom (Gₖ).hom =
      Y.hom ≫ (SmoothSite.torusOne Sₖ).left := by
    exact congrArg (fun f : Y ⟶ Gₖ ↦ f.left) (SmoothSite.productLift_snd _ _)
  apply Units.ext
  change (q ≫ pullback.snd Y.hom (Gₖ).hom).appTop (tₖ).val = 1
  rw [h, Category.assoc, hs, ← Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  let f : Γ(Sₖ, ⊤) →+* Γ(P, ⊤) := (g ≫ Y.hom).appTop.hom
  change f ((SmoothSite.torusOne Sₖ).left.appTop (tₖ).val) = 1
  exact (congrArg f hu).trans (map_one f)

section EqualSections

variable {X Y : SmoothSite (Spec (CommRingCat.of k))} {P : Scheme.{u}}
  (p : P ⟶ X.left) (q : P ⟶ Y.left) (h : p ≫ X.hom = q ≫ Y.hom)
  (s t : Γ(P, ⊤))

set_option quotPrecheck false in
local notation "Z₀(" u₀ ")" =>
  (AffineLineFiber.fiber (sectionToAffineLine (p ≫ X.hom) u₀) (0 : k))
set_option quotPrecheck false in
local notation "p₀(" u₀ ")" =>
  (AffineLineFiber.inclusion (sectionToAffineLine (p ≫ X.hom) u₀) (0 : k) ≫ p)

/-- Equal global equations give equal actual whole section cuts and cancel in the signed cut. -/
theorem signedSectionCutCorrespondence_eq_zero_of_section_eq
    [IsFinite (p₀(s))] [IsFinite (p₀(t))]
    (hs : ∀ x : genericPoints Z₀(s), p₀(s) x.val ∈ genericPoints X.left)
    (ht : ∀ x : genericPoints Z₀(t), p₀(t) x.val ∈ genericPoints X.left)
    (he : s = t) :
    signedSectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := P) p q h s t hs ht = 0 := by
  subst t
  exact sub_self (sectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := P) p q h s hs)

end EqualSections

variable (X Y : SmoothSite (Spec (CommRingCat.of k))) (z : torusPowerCutAmbient k X Y)

set_option quotPrecheck false in
local notation "Pz" => (integralComponentAt z).subscheme
local notation "pT" => torusPowerCutSource k X Y z
local notation "qT" => torusPowerCutTarget k X Y z
local notation "pX" => torusSupportBaseProjection k (X := X) (P := Pz) pT
local notation "qY" => torusSupportBaseProjection k (X := Y) (P := Pz) qT
local notation "t₁" => torusSupportCoordinate k (X := X) (P := Pz) pT
local notation "t₂" => torusSupportCoordinate k (X := Y) (P := Pz) qT
set_option quotPrecheck false in
local notation "p₀(" u₀ ")" =>
  (AffineLineFiber.inclusion (sectionToAffineLine (pX ≫ X.hom) u₀) (0 : k) ≫ pX)

/-- A native admissible prime with constant unit target has zero power cut. -/
theorem torusPowerCutPrime_eq_zero_of_target_unit (n : ℕ)
    (hadm : TorusPowerCutAdmissibleAt k X Y z n) (ht : t₂ = 1) :
    torusPowerCutPrime k X Y z n hadm = 0 := by
  let s : Γ(Pz, ⊤) := torusPowerCutNumerator t₁ n
  let t : Γ(Pz, ⊤) := torusPowerCutDenominator t₁ t₂ n
  let : IsFinite (p₀(s)) := hadm.numerator_finite
  let : IsFinite (p₀(t)) := hadm.denominator_finite
  have hbase : pX ≫ X.hom = qY ≫ Y.hom := by
    simp only [torusSupportBaseProjection, Category.assoc, MorphismProperty.Over.w,
      torusPowerCutSource, torusPowerCutTarget]
  have he : s = t := by
    simp only [s, t, torusPowerCutNumerator, torusPowerCutDenominator, ht, Units.val_one]
  change signedSectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := Pz)
    pX qY hbase s t hadm.numerator_generic hadm.denominator_generic = 0
  exact signedSectionCutCorrespondence_eq_zero_of_section_eq pX qY hbase s t
    hadm.numerator_generic hadm.denominator_generic he

end AlgebraicGeometry.Cor
