/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteFlatZeros

/-!
# Restriction of a whole closed support along an open immersion

The comparison uses the actual pullback of the closed scheme and identifies
its literal inclusion. This preserves the complete scheme structure.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- Restricting the ambient scheme along an open preserves the factorization of
the entire support through a smaller open in that ambient scheme. -/
theorem comap_whole_support_subset_of_open_factor {C R X : Scheme.{u}}
    (j : C ⟶ X) [IsOpenImmersion j] (i : R ⟶ C) (I : X.IdealSheafData)
    (hI : Set.range I.subschemeι ⊆ Set.range (i ≫ j)) :
    Set.range (I.comap j).subschemeι ⊆ Set.range i := by
  intro x hx
  rw [(I.comap j).range_subschemeι, Scheme.IdealSheafData.support_comap] at hx
  change j x ∈ I.support at hx
  have hx' : j x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hx
  obtain ⟨y, hy⟩ := hI hx'
  exact ⟨y, j.isOpenEmbedding.injective (by simpa only [Scheme.Hom.comp_apply] using hy)⟩

/-- An open containing the whole closed support identifies its actual pullback
scheme and inclusion map. -/
theorem exists_openSupportIso {A B : Scheme.{u}} (i : A ⟶ B) [IsOpenImmersion i]
    (I : B.IdealSheafData) (J : A.IdealSheafData) (hJ : J = I.comap i)
    (hI : Set.range I.subschemeι ⊆ Set.range i) :
    ∃ e : J.subscheme ≅ I.subscheme, e.hom ≫ I.subschemeι = J.subschemeι ≫ i := by
  subst J
  have := isIso_pullback_snd_of_whole_support i I hI
  let e := I.comapIso i ≪≫ asIso (pullback.snd i I.subschemeι)
  refine ⟨e, ?_⟩
  change ((I.comapIso i).hom ≫ pullback.snd i I.subschemeι) ≫ I.subschemeι = _
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, I.comapIso_hom_fst]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
