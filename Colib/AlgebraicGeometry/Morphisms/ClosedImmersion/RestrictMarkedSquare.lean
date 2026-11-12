/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restricting a marked Cartesian square to an open of the target

The original section restricts to the actual inverse images of the
chosen open. The restricted Cartesian square retains the identity on
the full marked scheme over that open.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} {f : Y ⟶ X} {z : Z ⟶ X} {s : Z ⟶ Y}
  (H : IsPullback s (𝟙 Z) f z) (U : X.Opens)

include H in
private theorem markedSection_preimage :
    z ⁻¹ᵁ U = s ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage]
  exact congrArg (fun m : Z ⟶ X ↦ m ⁻¹ᵁ U) (by
    simpa only [Category.id_comp] using H.w.symm)

/-- The literal restriction of the original marked section. -/
@[no_expose]
def restrictMarkedSection : (z ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
  s.resLE _ _ (markedSection_preimage H U).le

/-- Restriction preserves the actual map to the original source. -/
@[reassoc (attr := simp)]
theorem restrictMarkedSection_ι :
    restrictMarkedSection H U ≫ (f ⁻¹ᵁ U).ι = (z ⁻¹ᵁ U).ι ≫ s :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The whole original marked square stays Cartesian after open restriction. -/
theorem restrictMarkedSection_isPullback :
    IsPullback (restrictMarkedSection H U) (𝟙 _) (f ∣_ U) (z ∣_ U) := by
  have hU : z ⁻¹ᵁ U = s ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ (𝟙 Z) ⁻¹ᵁ (z ⁻¹ᵁ U) := by
    rw [← markedSection_preimage H U]
    simp
  have h := Scheme.Hom.isPullback_resLE H
    (US := U) (UT := z ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U) le_rfl le_rfl hU
  have hid : Scheme.Hom.resLE (𝟙 Z) (z ⁻¹ᵁ U) (z ⁻¹ᵁ U) (by simp) = 𝟙 _ := by
    apply (cancel_mono (z ⁻¹ᵁ U).ι).mp
    simp
  simpa only [restrictMarkedSection, Scheme.Hom.resLE_eq_morphismRestrict, hid] using h

/-- Restricting the whole target preserves the original full complement. -/
theorem range_morphismRestrict_complement {X A Z : Scheme.{u}}
    (a : A ⟶ X) (z : Z ⟶ X) (V : X.Opens)
    (hz : Set.range z = (Set.range a)ᶜ) :
    Set.range (z ∣_ V) = (Set.range (a ∣_ V))ᶜ := by
  have mem (Y : Scheme.{u}) (g : Y ⟶ X) (x : V.toScheme) :
      x ∈ Set.range (g ∣_ V) ↔ V.ι x ∈ Set.range g := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, (congrArg (fun f => f y) (morphismRestrict_ι g V)).symm⟩
    · rintro ⟨y, hy⟩
      have hym : y ∈ g ⁻¹ᵁ V := by change g y ∈ V; rw [hy]; exact x.property
      refine ⟨⟨y, hym⟩, ?_⟩
      apply V.ι.isOpenEmbedding.injective
      exact (congrArg (fun f => f ⟨y, hym⟩) (morphismRestrict_ι g V)).trans hy
  ext x
  rw [Set.mem_compl_iff, mem, mem, hz]
  rfl

end AlgebraicGeometry.Scheme
