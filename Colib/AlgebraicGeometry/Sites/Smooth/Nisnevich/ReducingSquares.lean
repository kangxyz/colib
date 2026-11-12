/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.StandardDensityRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.Ordinary.OpenBaseRefinement
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DensityOpens

/-!
# Geometric Nisnevich squares are reducing

The geometric choice of the two opens is realized by the existing open-base
refinement of the actual pullback square. Keeping the entire inverse image of the
closed complement preserves its scheme structure. Each of the three maps to
the original square factors through the corresponding prescribed open immersion.

See [Voevodsky, Proposition 2.9](https://arxiv.org/pdf/0805.4576#page=6).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
private theorem exists_factor_of_range_subset {Y U X : SmoothSite S}
    (f : Y ⟶ X) (j : U ⟶ X) [IsOpenImmersion j.left]
    (h : Set.range f.left ⊆ Set.range j.left) :
    ∃ g : Y ⟶ U, g ≫ j = f := by
  let g := IsOpenImmersion.lift j.left f.left h
  have hg : g ≫ j.left = f.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨homMk g ?_, ?_⟩
  · rw [← MorphismProperty.Over.w j, ← Category.assoc, hg, MorphismProperty.Over.w f]
  · apply MorphismProperty.Over.Hom.ext
    exact hg

variable [IsNoetherian S]

set_option backward.isDefEq.respectTransparency false in
/-- Over a noetherian base, the geometric Nisnevich squares are reducing
for the standard density filtration on the smooth site. -/
theorem geometricNisnevichSquares_reduce :
    NisnevichSquaresReduce (S := S) IsGeometricNisnevichSquare := by
  intro Q hQ d B A V j₁ j₂ j₃ h₁ h₂ h₃
  let : IsOpenImmersion Q.f₂₄.left := hQ.isOpenImmersion
  let : Etale Q.f₃₄.left := hQ.etale
  have hpb : IsPullback Q.f₁₂.left Q.f₁₃.left Q.f₂₄.left Q.f₃₄.left :=
    (forgetScheme S).map_isPullback hQ.isPullback
  let : IsOpenImmersion Q.f₁₃.left :=
    MorphismProperty.of_isPullback hpb inferInstance
  let : IsOpenImmersion j₁.left := h₁.isOpenImmersion
  let : IsOpenImmersion j₂.left := h₂.isOpenImmersion
  let : IsOpenImmersion j₃.left := h₃.isOpenImmersion
  have hfac : Q.f₁₂.left ≫ Q.f₂₄.left = Q.f₁₃.left ≫ Q.f₃₄.left :=
    congrArg (fun g ↦ g.left) Q.fac
  obtain ⟨O, T, hO, hA, _, hV, hB, hretain⟩ :=
    Nisnevich.exists_density_reducingOpens Q.f₁₂.left Q.f₁₃.left Q.f₂₄.left Q.f₃₄.left
      hfac h₂.density h₃.density h₁.density
  obtain ⟨Z, z, hz, hcomp, hi⟩ := hQ.complement
  let : IsClosedImmersion z := hz
  let : IsIso (pullback.snd Q.f₃₄.left z) := hi
  let Q' := ordinaryOpenBaseSquare Q.f₂₄ Q.f₃₄ O T
  let ψ := ordinaryOpenBaseSquareMap Q.f₂₄ Q.f₃₄ O T
  let φ : Q' ⟶ Q := {
    τ₁ := ψ.τ₁ ≫ hQ.isPullback.isoPullback.inv
    τ₂ := ψ.τ₂
    τ₃ := ψ.τ₃
    τ₄ := ψ.τ₄
    comm₁₂ := by
      rw [Category.assoc, hQ.isPullback.isoPullback_inv_fst]
      exact ψ.comm₁₂
    comm₁₃ := by
      rw [Category.assoc, hQ.isPullback.isoPullback_inv_snd]
      exact ψ.comm₁₃
    comm₂₄ := ψ.comm₂₄
    comm₃₄ := ψ.comm₃₄ }
  have hkeep (v : Q.X₃.left) (hv : Q.f₃₄.left v ∈ Set.range z)
      (hvo : Q.f₃₄.left v ∈ O) : v ∈ T := by
    rw [hcomp] at hv
    exact hretain v hvo (fun h ↦ hv (Scheme.Hom.mem_opensRange.mp h))
  have hQ' : IsGeometricNisnevichSquare Q' := {
    isPullback := IsPullback.of_hasPullback _ _
    isOpenImmersion := inferInstanceAs (IsOpenImmersion (ordinaryOpenRestrict Q.f₂₄ O).left)
    etale := inferInstanceAs (Etale (ordinaryOpenBaseEtaleMap Q.f₃₄ O T).left)
    complement := ⟨_, z ∣_ O,
      MorphismProperty.of_isPullback (isPullback_morphismRestrict z O).flip inferInstance,
      ordinaryOpenBaseSquare_complement Q.f₂₄ Q.f₃₄ O T z hcomp,
      ordinaryOpenBaseSquare_iso_complement Q.f₂₄ Q.f₃₄ O T z hkeep⟩ }
  refine ⟨Q', hQ', φ, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstanceAs (IsOpenImmersion O.ι), ?_⟩
    change O.ι.opensRange.IsInStandardDensity (d + 1)
    rwa [Scheme.Opens.opensRange_ι]
  · apply exists_factor_of_range_subset φ.τ₁ j₁
    rintro _ ⟨x, rfl⟩
    apply Scheme.Hom.mem_opensRange.mp
    apply hB
    change Q.f₁₃.left (φ.τ₁.left x) ∈ T
    have h : φ.τ₃.left (Q'.f₁₃.left x) = Q.f₁₃.left (φ.τ₁.left x) :=
      congrArg (fun g : Q'.X₁ ⟶ Q.X₃ ↦ g.left x) φ.comm₁₃
    rw [← h]
    exact (Q'.f₁₃.left x).property.2
  · apply exists_factor_of_range_subset φ.τ₂ j₂
    rintro _ ⟨x, rfl⟩
    exact Scheme.Hom.mem_opensRange.mp (hA x.property)
  · apply exists_factor_of_range_subset φ.τ₃ j₃
    rintro _ ⟨x, rfl⟩
    exact Scheme.Hom.mem_opensRange.mp (hV x.property.2)

end AlgebraicGeometry.Scheme.SmoothSite
