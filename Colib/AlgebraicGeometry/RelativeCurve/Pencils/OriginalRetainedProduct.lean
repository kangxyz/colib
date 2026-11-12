/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedBoundaryCover

/-!
# The retained product in the original target open

Passing from the retained target to the original target keeps the infinity
boundary. The marked boundary is contained in the original target open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S B C V Y Z D : Scheme.{u}}
  (b : B ⟶ S) (π : C ⟶ S) (v : V ⟶ C) (j : Y ⟶ C)
  (u : V ⟶ Y) (hu : u ≫ j = v)

include hu in
/-- The actual map of retained products induced by the given target inclusion. -/
def retainedProductOpenFactor : retainedProduct b π v ⟶ retainedProduct b π j :=
  pullback.lift (pullback.fst b (v ≫ π)) (pullback.snd b (v ≫ π) ≫ u)
    (by rw [Category.assoc, ← Category.assoc u j π, hu, pullback.condition])

@[reassoc (attr := simp)]
theorem retainedProductOpenFactor_fst :
    retainedProductOpenFactor b π v j u hu ≫ pullback.fst b (j ≫ π) =
      pullback.fst b (v ≫ π) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem retainedProductOpenFactor_snd :
    retainedProductOpenFactor b π v j u hu ≫ pullback.snd b (j ≫ π) =
      pullback.snd b (v ≫ π) ≫ u := pullback.lift_snd _ _ _

@[reassoc]
theorem retainedProductOpenFactor_inclusion :
    retainedProductOpenFactor b π v j u hu ≫ retainedProductInclusion b π j =
      retainedProductInclusion b π v := by
  apply pullback.hom_ext
  · simp only [Category.assoc, retainedProductInclusion_fst, retainedProductOpenFactor_fst]
  · simp only [Category.assoc, retainedProductInclusion_snd,
      retainedProductOpenFactor_snd_assoc, hu]

instance [IsOpenImmersion v] [IsOpenImmersion j] :
    IsOpenImmersion (retainedProductOpenFactor b π v j u hu) := by
  have : IsOpenImmersion
      (retainedProductOpenFactor b π v j u hu ≫ retainedProductInclusion b π j) := by
    rw [retainedProductOpenFactor_inclusion]
    infer_instance
  exact IsOpenImmersion.of_comp (retainedProductOpenFactor b π v j u hu)
    (retainedProductInclusion b π j)

include u hu in
/-- The original product and infinity already cover the complete compactified
product, since both the retained target and the marked target lie in the original open. -/
theorem originalRetainedProduct_infinity_cover (s : Z ⟶ Y) (d : D ⟶ C)
    (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j)) :
    ∀ x : (pullback b π : Scheme.{u}), x ∈ Set.range (retainedProductInclusion b π j) ∨
      x ∈ Set.range (pullback.fst (pullback.snd b π) d) := by
  intro x
  rcases hc (pullback.snd b π x) with ⟨w, hw⟩ | hd | ⟨w, hw⟩
  · obtain ⟨y, _, hy⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback b π j) (u w) x
      (by simpa only [← Scheme.Hom.comp_apply, hu] using hw)
    exact Or.inl ⟨y, hy⟩
  · right
    rw [Scheme.Pullback.range_fst]
    exact hd
  · obtain ⟨y, _, hy⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback b π j) (s w) x hw
    exact Or.inl ⟨y, hy⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
