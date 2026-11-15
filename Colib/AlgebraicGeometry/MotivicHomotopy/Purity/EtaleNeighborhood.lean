/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Étale neighborhoods preserving a closed subscheme

An étale morphism with a lift of a closed subscheme can be restricted to an
open neighborhood of that lift so that its entire inverse image is the given
closed subscheme. The proof removes the complementary part of the étale
fibre over the closed subscheme. This is the shrinking step in the common
étale neighborhood used by the local purity argument.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- An étale lift of a closed subscheme becomes an étale neighborhood inducing
the identity on that closed subscheme after restricting to an open neighborhood. -/
theorem exists_open_isPullback_of_etale_lift
    {Z X V : Scheme.{u}} (i : Z ⟶ X) (f : V ⟶ X)
    [IsClosedImmersion i] [Etale f] (s : Z ⟶ V) (hs : s ≫ f = i) :
    ∃ (U : V.Opens) (s' : Z ⟶ U.toScheme),
      s' ≫ U.ι = s ∧ IsPullback s' (𝟙 Z) (U.ι ≫ f) i := by
  let a : Z ⟶ pullback f i := pullback.lift s (𝟙 Z) (by simpa using hs)
  have ha : a ≫ pullback.snd f i = 𝟙 Z := pullback.lift_snd _ _ _
  have : Unramified (pullback.snd f i) :=
    (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).2
      ⟨inferInstance, inferInstance⟩
  have : IsOpenImmersion a := isOpenImmersion_of_isSection (pullback.snd f i) a ha
  let b : pullback f i ⟶ V := pullback.fst f i
  have hab : a ≫ b = s := pullback.lift_fst _ _ _
  have hbinj : Function.Injective b := b.isClosedEmbedding.injective
  have hclosed : IsClosed (b '' (Set.range a)ᶜ) :=
    b.isClosedEmbedding.isClosedMap _ a.isOpenEmbedding.isOpen_range.isClosed_compl
  let U : V.Opens := ⟨(b '' (Set.range a)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hsU : Set.range s ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩ ⟨w, hw, hbw⟩
    apply hw
    refine ⟨z, hbinj ?_⟩
    exact (congrArg (fun g : Z ⟶ V => g z) hab).trans hbw.symm
  let s' : Z ⟶ U.toScheme := IsOpenImmersion.lift U.ι s hsU
  have hs' : s' ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hpre : b ⁻¹ᵁ U.ι.opensRange = a.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    ext w
    change b w ∉ b '' (Set.range a)ᶜ ↔ w ∈ Set.range a
    constructor
    · intro hw
      by_contra h
      exact hw ⟨w, h, rfl⟩
    · rintro ⟨z, rfl⟩ ⟨w, hw, hbw⟩
      exact hw ⟨z, hbinj hbw.symm⟩
  have hleft : IsPullback a s' b U.ι :=
    (IsOpenImmersion.isPullback s' a U.ι b (hab.trans hs'.symm) hpre).flip
  have hwhole := hleft.paste_horiz (IsPullback.of_hasPullback f i).flip
  refine ⟨U, s', hs', ?_⟩
  simpa only [ha] using hwhole.flip

/-- The restricted étale neighborhood induces an isomorphism on the scheme-theoretic
inverse image of the closed subscheme. -/
theorem exists_open_isIso_pullback_of_etale_lift
    {Z X V : Scheme.{u}} (i : Z ⟶ X) (f : V ⟶ X)
    [IsClosedImmersion i] [Etale f] (s : Z ⟶ V) (hs : s ≫ f = i) :
    ∃ (U : V.Opens) (s' : Z ⟶ U.toScheme),
      s' ≫ U.ι = s ∧ Etale (U.ι ≫ f) ∧
        IsPullback s' (𝟙 Z) (U.ι ≫ f) i ∧ IsIso (pullback.snd (U.ι ≫ f) i) := by
  obtain ⟨U, s', hs', hpb⟩ := exists_open_isPullback_of_etale_lift i f s hs
  have : IsIso (hpb.isoPullback.hom ≫ pullback.snd (U.ι ≫ f) i) := by
    rw [hpb.isoPullback_hom_snd]
    infer_instance
  exact ⟨U, s', hs', inferInstance, hpb,
    IsIso.of_isIso_comp_left hpb.isoPullback.hom (pullback.snd (U.ι ≫ f) i)⟩

end AlgebraicGeometry

end
