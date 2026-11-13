/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Additive
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Support
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor

/-!
# Weighted power cuts on finite correspondences

For a fixed exponent, the power cut is additive on the subgroup whose prime
supports admit the two cuts. The map is the signed sum in the native
correspondence groups, with the original integer coefficient at each point.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme AffineLineFiber

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
variable (X Y : SmoothSite (Spec (CommRingCat.of k)))

local notation "XG" => SmoothSite.product X Gₘ
local notation "YG" => SmoothSite.product Y Gₘ

local notation "D" => torusPowerCutAmbient k X Y
local notation "C₁" => (Cor.mk (XG) ⟶ Cor.mk (YG))
local notation "C₀" => (Cor.mk X ⟶ Cor.mk Y)

variable (z : torusPowerCutAmbient k X Y)

local notation "pₜ" => torusPowerCutSource k X Y z
local notation "qₜ" => torusPowerCutTarget k X Y z
set_option quotPrecheck false in
local notation "Pₜ" => (integralComponentAt (X := D) z).subscheme
local notation "pₓ" => torusSupportBaseProjection k (X := X) (P := Pₜ) pₜ
local notation "qᵧ" => torusSupportBaseProjection k (X := Y) (P := Pₜ) qₜ
local notation "t₁" => torusSupportCoordinate k (X := X) (P := Pₜ) pₜ
local notation "t₂" => torusSupportCoordinate k (X := Y) (P := Pₜ) qₜ
local notation "N(" n ")" => torusPowerCutNumerator t₁ n
local notation "Den(" n ")" => torusPowerCutDenominator t₁ t₂ n
set_option quotPrecheck false in
local notation "Z₀(" s ")" => AffineLineFiber.fiber (sectionToAffineLine (pₓ ≫ X.hom) s) 0
set_option quotPrecheck false in
local notation "p₀(" s ")" =>
  AffineLineFiber.inclusion (sectionToAffineLine (pₓ ≫ X.hom) s) 0 ≫ pₓ

/-- Both literal zero schemes are finite and every component lies over a
generic point of the source. -/
structure TorusPowerCutAdmissibleAt (n : ℕ) : Prop where
  numerator_finite : IsFinite (p₀(N(n)))
  denominator_finite : IsFinite (p₀(Den(n)))
  numerator_generic : ∀ a : genericPoints Z₀(N(n)), p₀(N(n)) a.val ∈ genericPoints X.left
  denominator_generic : ∀ a : genericPoints Z₀(Den(n)), p₀(Den(n)) a.val ∈ genericPoints X.left

/-- The signed cut of an actual prime support. -/
def torusPowerCutPrime (n : ℕ) (h : TorusPowerCutAdmissibleAt k X Y z n) : C₀ := by
  let : IsFinite (p₀(N(n))) := h.numerator_finite
  let : IsFinite (p₀(Den(n))) := h.denominator_finite
  refine signedSectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := Pₜ) pₓ qᵧ ?_
    (N(n)) (Den(n)) h.numerator_generic h.denominator_generic
  simp only [torusSupportBaseProjection, Category.assoc, MorphismProperty.Over.w,
    torusPowerCutSource, torusPowerCutTarget]

variable (n : ℕ)

set_option maxHeartbeats 800000 in
-- Identifying the Cor operations with their pointwise cycle operations unfolds the native product.
/-- The subgroup on which the fixed-exponent power cut is defined. -/
def torusPowerCutDomain : AddSubgroup C₁ where
  carrier := {a | ∀ z, a.val z ≠ 0 → TorusPowerCutAdmissibleAt k X Y z n}
  zero_mem' := by
    intro z hz
    change (0 : ℤ) ≠ 0 at hz
    exact (hz rfl).elim
  add_mem' := by
    intro a b ha hb z hz
    change a.val z + b.val z ≠ 0 at hz
    by_cases h : a.val z = 0
    · exact hb z (fun h' => hz ((congrArg₂ (fun r s : ℤ => r + s) h h').trans (zero_add 0)))
    · exact ha z h
  neg_mem' := by
    intro a ha z hz
    change -a.val z ≠ 0 at hz
    exact ha z (fun h => hz ((congrArg (fun r : ℤ => -r) h).trans neg_zero))

/-- Membership checks just the prime supports with nonzero coefficients. -/
theorem mem_torusPowerCutDomain_iff (a : C₁) :
    a ∈ torusPowerCutDomain k X Y n ↔
      ∀ z, a.val z ≠ 0 → TorusPowerCutAdmissibleAt k X Y z n := Iff.rfl

/-- A signed prime belongs to the domain when its support admits the cuts. -/
theorem single_mem_torusPowerCutDomain
    (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z)
    (h : TorusPowerCutAdmissibleAt k X Y z n) (r : ℤ) :
    singleFiniteCorrespondence (XG).hom (YG).hom z hz r ∈ torusPowerCutDomain k X Y n := by
  classical
  rw [mem_torusPowerCutDomain_iff]
  intro w hw
  by_cases he : w = z
  · exact he.symm ▸ h
  · exfalso
    apply hw
    let z' : pullback (C := Scheme) (XG).hom (YG).hom := z
    change (single z' r) w = 0
    exact (single_apply (x₁ := z') (x₂ := w) (y := r)).trans (ite_eq_right he)

attribute [local instance] Classical.propDecidable

/-- The power cut on native finite correspondences with admissible support. -/
def torusPowerCut : torusPowerCutDomain k X Y n →+ C₀ :=
  (liftFiniteCorrespondence (XG).hom (YG).hom
    (fun z _ => if h : TorusPowerCutAdmissibleAt k X Y z n then
      torusPowerCutPrime k X Y z n h else 0)).comp (torusPowerCutDomain k X Y n).subtype

/-- The cut retains the original signed coefficient of an admissible prime. -/
theorem torusPowerCut_single (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z)
    (h : TorusPowerCutAdmissibleAt k X Y z n) (r : ℤ) :
    torusPowerCut k X Y n
      ⟨singleFiniteCorrespondence (XG).hom (YG).hom z hz r,
        single_mem_torusPowerCutDomain k X Y z n hz h r⟩ =
      r • torusPowerCutPrime k X Y z n h := by
  let φ (w : pullback (C := Scheme) (XG).hom (YG).hom)
      (_ : IsFiniteCorrespondencePoint (XG).hom (YG).hom w) : C₀ :=
    if hw : TorusPowerCutAdmissibleAt k X Y w n then torusPowerCutPrime k X Y w n hw else 0
  change liftFiniteCorrespondence (XG).hom (YG).hom φ
    (singleFiniteCorrespondence (XG).hom (YG).hom z hz r) = _
  calc
    _ = r • φ z hz := liftFiniteCorrespondence_single (XG).hom (YG).hom φ z hz r
    _ = _ := congrArg (r • ·) (dite_eq_left h)

end AlgebraicGeometry.Cor
