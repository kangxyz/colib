/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Weighted
import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.GenericImage
import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.QuasiCompact
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-!
# Eventual admissibility of the native power cut

A prime correspondence admits both cuts for every sufficiently large
exponent. The cut on any finite correspondence, or a finite family of them,
therefore has a single exponent bound. The source may be disconnected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin

universe u v

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.NativeTorusPolynomial

variable (k : Type u) [Field k]
  (X Y : SmoothSite (Spec (CommRingCat.of k)))

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "XG" => (SmoothSite.product X Gₘ)
local notation "YG" => (SmoothSite.product Y Gₘ)

/-- Both cuts of every actual prime support have finite support and generic
images over the original source for all large exponents. -/
theorem exists_torusPowerCutAdmissibleAt (z : torusPowerCutAmbient k X Y)
    (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → TorusPowerCutAdmissibleAt k X Y z n := by
  let P := (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subscheme
  let g := torusPowerCutSource k X Y z
  let v := torusPowerCutTarget k X Y z
  let f : X.left ⟶ Sₖ := X.hom
  let p := torusSupportBaseProjection k g
  let u := torusSupportCoordinate k v
  let t := torusSupportCoordinate k g
  let b := p ≫ f
  let : IsFinite g := hz.1
  let : IsIntegral P := isIntegral_integralComponentAt z
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (Y := Sₖ) (g ≫ (XG).hom)
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (Y := (XG).left) g
  let : IsNoetherian P := ⟨⟩
  have hgeneric := sectionCut_nonzero_and_generic_of_finite_torus_component f g hz.2
  obtain ⟨N, hN⟩ := exists_isFinite_power_sub_unit_of_compactSpace f g u
  refine ⟨N, fun n hn => ?_⟩
  have hnum : IsFinite (AffineLineFiber.inclusion
      (sectionToAffineLine b (torusPowerCutNumerator t n)) 0 ≫ p) :=
    isFinite_power_sub_one_of_compactSpace f g (Nat.succ_pos n)
  have hden : IsFinite (AffineLineFiber.inclusion
      (sectionToAffineLine b (torusPowerCutDenominator t u n)) 0 ≫ p) :=
    hN (n + 1) (hn.trans (Nat.le_succ n))
  exact ⟨hnum, hden, (hgeneric _ hnum).2, (hgeneric _ hden).2⟩

/-- The actual finite support of a correspondence admits one common exponent bound. -/
theorem exists_mem_torusPowerCutDomain (a : Cor.mk XG ⟶ Cor.mk YG) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a ∈ torusPowerCutDomain k X Y n := by
  classical
  let : Finite a.val.support := a.property.1.to_subtype
  let : Fintype a.val.support := Fintype.ofFinite _
  choose N hN using fun z : a.val.support =>
    exists_torusPowerCutAdmissibleAt k X Y z.val (a.property.2 z.val z.property)
  refine ⟨Finset.univ.sup N, fun n hn => (mem_torusPowerCutDomain_iff k X Y n a).mpr ?_⟩
  intro z hz
  let w : a.val.support := ⟨z, hz⟩
  exact hN w n ((Finset.le_sup (Finset.mem_univ w)).trans hn)

/-- A finite family of correspondences, with possibly different source and
target schemes, admits a common power-cut exponent bound. -/
theorem exists_mem_torusPowerCutDomain_family {ι : Type v} [Finite ι]
    (X₀ Y₀ : ι → SmoothSite (Spec (CommRingCat.of k)))
    (a : ∀ i, Cor.mk (SmoothSite.product (X₀ i) Gₘ) ⟶ Cor.mk (SmoothSite.product (Y₀ i) Gₘ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i, a i ∈ torusPowerCutDomain k (X₀ i) (Y₀ i) n := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  choose N hN using fun i => exists_mem_torusPowerCutDomain k (X₀ i) (Y₀ i) (a i)
  refine ⟨Finset.univ.sup N, fun n hn i => ?_⟩
  exact hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)

end AlgebraicGeometry.Cor
