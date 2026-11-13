/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphExterior.SectionCut
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Weighted
public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport
public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointCycle
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters

/-!
# Power-cut normalization on the native exterior identity prime

The isomorphism from the literal diagonal-parameter support to the native
prime support identifies both source and target maps. Transporting the
two whole section cuts through this isomorphism gives the original prime,
with its positive coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NativeTorusPolynomial Stacks.Chow
open AlgebraicGeometry.Scheme TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => SmoothSite.multiplicativeGroupObject Sₖ

variable (X Y : SmoothSite (Spec (CommRingCat.of k))) (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation "zG" => nativeExteriorPoint X Y Gₖ z hz
local notation "W" => integralComponentAt z
local notation "D" => exteriorIdentitySupport X Y Gₖ W
set_option quotPrecheck false in
local notation "Pz" => (integralComponentAt zG).subscheme
local notation "e" => nativeExteriorSupportIso X Y Gₖ z hz
local notation "pT" => torusPowerCutSource k X Y zG
local notation "qT" => torusPowerCutTarget k X Y zG
set_option quotPrecheck false in
local notation "pX" => torusSupportBaseProjection k (X := X) (P := Pz) pT
set_option quotPrecheck false in
local notation "qY" => torusSupportBaseProjection k (X := Y) (P := Pz) qT
set_option quotPrecheck false in
local notation "t₁" => torusSupportCoordinate k (X := X) (P := Pz) pT
set_option quotPrecheck false in
local notation "t₂" => torusSupportCoordinate k (X := Y) (P := Pz) qT
set_option quotPrecheck false in
local notation "bW" => exteriorSupportSourceProjection X Y W ≫ X.hom
set_option quotPrecheck false in
local notation "pD" => (e).hom ≫ pX
set_option quotPrecheck false in
local notation "qD" => (e).hom ≫ qY
set_option quotPrecheck false in
local notation "πW" => pullback.fst bW (Gₖ).hom
local notation "pW" => exteriorSupportSourceProjection X Y W
local notation "qW" => exteriorSupportTargetProjection X Y W

private abbrev exteriorGraphCoordinate : Γ(D, ⊤) := torusGraphCoordinate bW

set_option quotPrecheck false in
local notation "tD" => exteriorGraphCoordinate k X Y z

private theorem exterior_prime_section_maps :
    ((e).hom ≫ pT = exteriorIdentitySource X Y Gₖ W) ∧
      ((e).hom ≫ qT = exteriorIdentityTarget X Y Gₖ W) :=
  ⟨nativeExteriorSupportIso_hom_source X Y Gₖ z hz,
    nativeExteriorSupportIso_hom_target X Y Gₖ z hz⟩

private theorem exterior_prime_coordinates :
    (e).hom.appTop (t₁ : Γ(Pz, ⊤)) = tD ∧
      (e).hom.appTop (t₂ : Γ(Pz, ⊤)) = tD := by
  obtain ⟨hp, hq⟩ := exterior_prime_section_maps k X Y z hz
  obtain ⟨ht₁, ht₂⟩ := exteriorIdentity_coordinates X Y W
  constructor
  · change (e).hom.appTop ((pT ≫ pullback.snd X.hom (Gₖ).hom).appTop
      (multiplicativeGroupBaseChangeCoordinate Sₖ).val) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, hp]
    exact ht₁
  · change (e).hom.appTop ((qT ≫ pullback.snd Y.hom (Gₖ).hom).appTop
      (multiplicativeGroupBaseChangeCoordinate Sₖ).val) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, hq]
    exact ht₂

private theorem exterior_prime_base_maps :
    pD = πW ≫ pW ∧ qD = πW ≫ qW := by
  obtain ⟨hp, hq⟩ := exterior_prime_section_maps k X Y z hz
  constructor
  · change (e).hom ≫ pT ≫ pullback.fst X.hom (Gₖ).hom = _
    rw [← Category.assoc, hp, exteriorIdentitySource_fst]
  · change (e).hom ≫ qT ≫ pullback.fst Y.hom (Gₖ).hom = _
    rw [← Category.assoc, hq, exteriorIdentityTarget_fst]

private theorem exterior_prime_cut_sections (n : ℕ) :
    (e).hom.appTop (torusPowerCutNumerator t₁ n) = tD ^ (n + 1) - 1 ∧
      (e).hom.appTop (torusPowerCutDenominator t₁ t₂ n) = tD ^ (n + 1) - tD := by
  obtain ⟨ht₁, ht₂⟩ := exterior_prime_coordinates k X Y z hz
  constructor
  · simp only [torusPowerCutNumerator, map_sub, map_pow, map_one, ht₁]
  · simp only [torusPowerCutDenominator, map_sub, map_pow, ht₁, ht₂]

set_option quotPrecheck false in
local notation "i₀(" u₀ ")" =>
  (AffineLineFiber.inclusion (sectionToAffineLine (pX ≫ X.hom) u₀) (0 : k))
set_option quotPrecheck false in
local notation "i₁(" u₀ ")" =>
  (AffineLineFiber.inclusion (sectionToAffineLine (pD ≫ X.hom) u₀) (0 : k))
set_option quotPrecheck false in
local notation "Z₀(" u₀ ")" =>
  (AffineLineFiber.fiber (sectionToAffineLine (pX ≫ X.hom) u₀) (0 : k))

private theorem exterior_prime_lift_cut_admissible (u₀ : Γ(Pz, ⊤))
    (hF : IsFinite (i₁((e).hom.appTop u₀) ≫ πW) ∧ Flat (i₁((e).hom.appTop u₀) ≫ πW)) :
    IsFinite (i₀(u₀) ≫ pX) ∧
      ∀ a : genericPoints Z₀(u₀), (i₀(u₀) ≫ pX) a.val ∈ genericPoints X.left := by
  let r := i₁((e).hom.appTop u₀) ≫ πW
  let : IsFinite r := hF.1
  let : Flat r := hF.2
  let : IsFinite pW := hz.1
  let : IsIntegral (W).subscheme := isIntegral_integralComponentAt z
  have he : i₁((e).hom.appTop u₀) ≫ pD = r ≫ pW := by
    exact (congrArg (fun f : D ⟶ X.left => i₁((e).hom.appTop u₀) ≫ f)
      (exterior_prime_base_maps k X Y z hz).1).trans (Category.assoc _ _ _).symm
  refine ⟨(isFinite_sectionCut_supportIso_iff e u₀ pX).mp ?_,
    (sectionCut_generic_supportIso_iff e u₀ pX).mp ?_⟩
  · rw [he]
    infer_instance
  · intro a
    have ha := mem_genericPoints_of_flat r a.property
    have hap : r a.val = genericPoint (W).subscheme := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using ha
    rw [he, Scheme.Hom.comp_apply, hap]
    change pullback.fst X.hom Y.hom ((W).subschemeι (genericPoint (W).subscheme)) ∈ _
    rw [show (W).subschemeι (genericPoint (W).subscheme) = z from
      genericPointOf_integralComponentAt z]
    exact hz.source_mem_genericPoints

set_option maxHeartbeats 1000000 in
-- The actual finite flat cuts are transported through their dependent fiber types.
/-- The original exterior identity prime admits both power cuts for every positive exponent. -/
theorem nativeExteriorPoint_torusPowerCutAdmissibleAt (n : ℕ) (hn : n ≠ 0) :
    TorusPowerCutAdmissibleAt k X Y zG n := by
  let s : Γ(Pz, ⊤) := torusPowerCutNumerator t₁ n
  let t : Γ(Pz, ⊤) := torusPowerCutDenominator t₁ t₂ n
  have hb : pD ≫ X.hom = πW ≫ bW :=
    (congrArg (fun f : D ⟶ X.left => f ≫ X.hom)
      (exterior_prime_base_maps k X Y z hz).1).trans (Category.assoc πW pW X.hom)
  obtain ⟨hs, ht⟩ := exterior_prime_cut_sections k X Y z hz n
  have hs' : IsFinite (i₁((e).hom.appTop s) ≫ πW) ∧ Flat (i₁((e).hom.appTop s) ≫ πW) := by
    dsimp only [s]
    rw [hb, hs]
    exact torusGraphNumerator_isFinite_and_flat bW n
  have ht' : IsFinite (i₁((e).hom.appTop t) ≫ πW) ∧ Flat (i₁((e).hom.appTop t) ≫ πW) := by
    dsimp only [t]
    rw [hb, ht]
    exact torusGraphDenominator_isFinite_and_flat bW n hn
  obtain ⟨hsf, hsg⟩ := exterior_prime_lift_cut_admissible k X Y z hz s hs'
  obtain ⟨htf, htg⟩ := exterior_prime_lift_cut_admissible k X Y z hz t ht'
  exact ⟨hsf, htf, hsg, htg⟩

set_option maxHeartbeats 1000000 in
-- The exact two fiber comparisons retain all dependent finite-map instances.
/-- Voevodsky's diagonal power cut recovers the original native prime. -/
theorem torusPowerCutPrime_nativeExteriorPoint (n : ℕ) (hn : n ≠ 0)
    (hadm : TorusPowerCutAdmissibleAt k X Y zG n) :
    torusPowerCutPrime k X Y zG n hadm = singleFiniteCorrespondence X.hom Y.hom z hz 1 := by
  let s : Γ(Pz, ⊤) := torusPowerCutNumerator t₁ n
  let t : Γ(Pz, ⊤) := torusPowerCutDenominator t₁ t₂ n
  let s' := (e).hom.appTop s
  let t' := (e).hom.appTop t
  let : IsFinite (i₀(s) ≫ pX) := hadm.numerator_finite
  let : IsFinite (i₀(t) ≫ pX) := hadm.denominator_finite
  let : IsFinite (i₁(s') ≫ pD) :=
    (isFinite_sectionCut_supportIso_iff e s pX).2 hadm.numerator_finite
  let : IsFinite (i₁(t') ≫ pD) :=
    (isFinite_sectionCut_supportIso_iff e t pX).2 hadm.denominator_finite
  have hP : pX ≫ X.hom = qY ≫ Y.hom := by
    simp only [torusSupportBaseProjection, Category.assoc, MorphismProperty.Over.w,
      torusPowerCutSource, torusPowerCutTarget]
  have hD : pD ≫ X.hom = qD ≫ Y.hom := by
    calc
      _ = (e).hom ≫ (pX ≫ X.hom) := Category.assoc _ _ _
      _ = (e).hom ≫ (qY ≫ Y.hom) := congrArg (fun f : Pz ⟶ Sₖ => (e).hom ≫ f) hP
      _ = _ := (Category.assoc _ _ _).symm
  obtain ⟨hpD, hqD⟩ := exterior_prime_base_maps k X Y z hz
  obtain ⟨hs', ht'⟩ := exterior_prime_cut_sections k X Y z hz n
  have hsgen := (sectionCut_generic_supportIso_iff e s pX).2 hadm.numerator_generic
  have htgen := (sectionCut_generic_supportIso_iff e t pX).2 hadm.denominator_generic
  have hₛ := sectionCutCorrespondence_supportIso e s pX qY hP hadm.numerator_generic hsgen
  have hₜ := sectionCutCorrespondence_supportIso e t pX qY hP hadm.denominator_generic htgen
  change signedSectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := Pz)
    pX qY hP s t hadm.numerator_generic hadm.denominator_generic = _
  rw [signedSectionCutCorrespondence, ← hₛ, ← hₜ]
  exact signedSectionCutCorrespondence_exteriorIdentity X Y z hz pD qD s' t' hpD hqD hD n hn
    hs' ht' hsgen htgen

end AlgebraicGeometry.Cor
