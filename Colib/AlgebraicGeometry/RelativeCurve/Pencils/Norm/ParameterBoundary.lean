/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ParameterChange

/-!
# Pullback of a whole boundary unit along the first parameter

The original boundary is pulled back as a scheme. Its unit restriction and
its cover of the entire retained complement both survive that change.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S Y K P A D : Scheme.{u}} (b : Y ⟶ S) (b' : K ⟶ S)
  (α : K ⟶ Y) [IsOpenImmersion α] (hα : α ≫ b = b') (π : P ⟶ S)
  (a : A ⟶ P) (U : (pullback b π : Scheme.{u}).Opens)
  (l : D ⟶ U.toScheme) (r : Γ(pullback b π, U))

local notation "d" => (l ≫ Scheme.Opens.ι U ≫ pullback.fst b π)
local notation "ρ" => (retainedSourceChange b b' π α hα)
set_option quotPrecheck false in
local notation "W" => (ρ ⁻¹ᵁ U)

omit [IsOpenImmersion α] in
/-- The pulled boundary has a point over each point of the changed parameter
when the original boundary projects onto the whole first parameter. -/
theorem nonempty_boundary_parameterChange [Nonempty K] (hs : Function.Surjective d) :
    Nonempty (pullback α d : Scheme.{u}) := by
  let x : K := Classical.choice inferInstance
  obtain ⟨y, hy⟩ := hs (α x)
  obtain ⟨z, -, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback α d) x y hy.symm
  exact ⟨z⟩

include hα in
/-- The actual whole boundary after changing the first parameter still covers
the complement of the original retained second factor. The same unit has
value one through the literal boundary map. -/
theorem exists_boundary_parameterChange
    (hcover : (Set.range (retainedProductInclusion b π a))ᶜ ⊆ Set.range (l ≫ U.ι))
    (hunit : l.appTop (U.topIso.inv r) = 1) :
    ∃ l' : pullback α d ⟶ (W).toScheme,
      (Set.range (retainedProductInclusion b' π a))ᶜ ⊆ Set.range (l' ≫ (W).ι) ∧
      l'.appTop ((W).topIso.inv ((ρ).app U r)) = 1 := by
  let f := pullback.fst α d
  let g := pullback.snd α d
  have H := retainedSourceChange_isPullback b b' π α hα
  have h : (g ≫ l ≫ U.ι) ≫ pullback.fst b π = f ≫ α := by
    simpa only [Category.assoc, f, g] using (pullback.condition (f := α) (g := d)).symm
  let i := H.lift (g ≫ l ≫ U.ι) f h
  have hi : i ≫ ρ = g ≫ l ≫ U.ι := H.lift_fst _ _ _
  let : IsOpenImmersion ρ := MorphismProperty.of_isPullback H.flip inferInstance
  have hW : Set.range i ⊆ Set.range (W).ι := by
    rintro x ⟨y, rfl⟩
    rw [Opens.range_ι]
    change ρ (i y) ∈ U
    rw [← Hom.comp_apply, hi, Hom.comp_apply, Hom.comp_apply]
    exact (l (g y)).2
  let l' := IsOpenImmersion.lift (W).ι i hW
  have hl' : l' ≫ (W).ι = i := IsOpenImmersion.lift_fac _ _ _
  refine ⟨l', ?_, ?_⟩
  · intro x hx
    have hxρ : ρ x ∈ (Set.range (retainedProductInclusion b π a))ᶜ := by
      intro hmem
      apply hx
      apply (mem_range_retainedProductInclusion b' π a x).2
      have hz := (mem_range_retainedProductInclusion b π a (ρ x)).1 hmem
      rwa [← Hom.comp_apply, retainedSourceChange_snd] at hz
    obtain ⟨y, hy⟩ := hcover hxρ
    have hy' : α (pullback.fst b' π x) = d y := by
      change (pullback.fst b' π ≫ α) x = (l ≫ U.ι ≫ pullback.fst b π) y
      rw [← retainedSourceChange_fst b b' π α hα, Hom.comp_apply,
        ← hy, ← Hom.comp_apply, Category.assoc]
    obtain ⟨z, -, hzg⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback α d) (pullback.fst b' π x) y hy'
    refine ⟨z, ?_⟩
    rw [hl']
    apply (ρ).isOpenEmbedding.injective
    rw [← Hom.comp_apply, hi, Hom.comp_apply, hzg]
    exact hy
  · have hres : l' ≫ (ρ ∣_ U) = g ≫ l := by
      apply (cancel_mono U.ι).mp
      calc
        _ = l' ≫ (W).ι ≫ ρ := by rw [Category.assoc, morphismRestrict_ι]
        _ = (l' ≫ (W).ι) ≫ ρ := (Category.assoc _ _ _).symm
        _ = i ≫ ρ := congrArg (fun k ↦ k ≫ ρ) hl'
        _ = _ := by rw [hi, Category.assoc]
    have hTop : (ρ ∣_ U).appTop = U.topIso.hom ≫ (ρ).app U ≫ (W).topIso.inv := by
      have ht := (ρ).resLE_app_top (U := U) (V := W) le_rfl
      change ((ρ).resLE U W le_rfl).appTop = _ at ht
      rw [Hom.resLE_eq_morphismRestrict, Hom.appLE_eq_app] at ht
      exact ht
    have hR : (W).topIso.inv ((ρ).app U r) = (ρ ∣_ U).appTop (U.topIso.inv r) := by
      rw [hTop, CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rw [hR, ← CommRingCat.comp_apply, ← Hom.comp_appTop, hres, Hom.comp_appTop,
      CommRingCat.comp_apply, hunit, map_one]

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S K P A D Z : Scheme.{u}} (b : K ⟶ S) (π : P ⟶ S)
  (a : A ⟶ P) (d : D ⟶ P) (z : Z ⟶ P) (U : (pullback b π : Scheme.{u}).Opens)
  (l : pullback b (d ≫ π) ⨿ pullback b (z ≫ π) ⟶ U.toScheme)
  (hl : l ≫ U.ι = coprod.desc (retainedProductInclusion b π d)
    (retainedProductInclusion b π z))

include hl in
/-- The two actual boundary factors cover the retained complement when their
images and the retained open cover the original second factor. -/
theorem wholeBoundary_cover_of_secondFactor
    (hc : ∀ x : P, x ∈ Set.range a ∨ x ∈ Set.range d ∨ x ∈ Set.range z) :
    (Set.range (retainedProductInclusion b π a))ᶜ ⊆ Set.range (l ≫ U.ι) := by
  intro x hx
  rcases hc (pullback.snd b π x) with h | h | h
  · exact (hx ((mem_range_retainedProductInclusion b π a x).2 h)).elim
  · obtain ⟨y, hy⟩ := (mem_range_retainedProductInclusion b π d x).2 h
    exact ⟨(coprod.inl : pullback b (d ≫ π) ⟶ _) y, by
      rw [hl]
      simpa only [← Hom.comp_apply, coprod.inl_desc] using hy⟩
  · obtain ⟨y, hy⟩ := (mem_range_retainedProductInclusion b π z x).2 h
    exact ⟨(coprod.inr : pullback b (z ≫ π) ⟶ _) y, by
      rw [hl]
      simpa only [← Hom.comp_apply, coprod.inr_desc] using hy⟩

include hl in
/-- A boundary factor covering the coefficient base still covers the whole
first parameter after the original product construction. -/
theorem wholeBoundary_surjective_firstProjection (hd : Function.Surjective (d ≫ π)) :
    Function.Surjective (l ≫ U.ι ≫ pullback.fst b π) := by
  intro y
  obtain ⟨z, hz⟩ := hd (b y)
  obtain ⟨x, hxy, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback b (d ≫ π)) y z hz.symm
  refine ⟨(coprod.inl : pullback b (d ≫ π) ⟶ _) x, ?_⟩
  rw [← Category.assoc, hl]
  simpa only [← Hom.comp_apply, coprod.inl_desc_assoc, retainedProductInclusion_fst] using hxy

end AlgebraicGeometry.Scheme.RelativeCurvePencil
