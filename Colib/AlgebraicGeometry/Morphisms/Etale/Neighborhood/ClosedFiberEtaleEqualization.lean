/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.Basic


/-! # Ambient open refinement of equality on a closed fiber

Two maps from a closed subscheme into an etale relative target have an open
scheme-theoretic equalizer. Removing its closed complement in the ambient
scheme extends this equality to an actual ambient open. The original marking
is retained as a scheme morphism, not replaced by its image point.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Morphisms/Etale/Neighborhood/ClosedFiberEtaleEqualization.lean`,
blob `ea042f5d9cc114d269b709a4e259497a5225ec23`.
Actual etale scheme-theoretic equalizer and closed complement construct an ambient open preserving
the entire original marker.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Reuse the canonical equalizer theorem while retaining the instance interface.
attribute [instance] isOpenImmersion_equalizer_ι_left

namespace Scheme.Hom

/-- Equality along the full original mark extends to the closed fiber of an
actual ambient open. This is the arrow-equalization step for marked closed-fiber
neighborhood comparison; it makes no extension claim for arbitrary etale objects. -/
theorem exists_open_closedFiber_equalizes
    {S Y A : Scheme.{u}} {D V : Over S} [Etale V.hom]
    (i : D.left ⟶ Y) [IsClosedImmersion i]
    (f g : D ⟶ V) (a : A ⟶ D.left) (ha : a ≫ f.left = a ≫ g.left) :
    ∃ O : Y.Opens, Set.range (a ≫ i) ⊆ O ∧
      pullback.fst i O.ι ≫ f.left = pullback.fst i O.ι ≫ g.left := by
  let e : (equalizer f g).left ⟶ D.left := (equalizer.ι f g).left
  let B : Set Y := i '' (Set.range e)ᶜ
  have hB : IsClosed B := i.isClosedEmbedding.isClosedMap _
    e.isOpenEmbedding.isOpen_range.isClosed_compl
  let O : Y.Opens := ⟨Bᶜ, hB.isOpen_compl⟩
  have hO (d : D.left) : i d ∈ O ↔ d ∈ Set.range e := by
    change i d ∉ B ↔ d ∈ Set.range e
    simp only [B, Set.mem_image, Set.mem_compl_iff]
    constructor
    · intro hd
      by_contra hn
      exact hd ⟨d, hn, rfl⟩
    · intro hd
      rintro ⟨d', hd', he⟩
      exact hd' ((i.isClosedEmbedding.injective he).symm ▸ hd)
  let a' : Over.mk (a ≫ D.hom) ⟶ D := Over.homMk a rfl
  have ha' : a' ≫ f = a' ≫ g := by
    apply Over.OverMorphism.ext
    exact ha
  let l := (equalizer.lift a' ha').left
  have hl : l ≫ e = a := congrArg (fun t => t.left) (equalizer.lift_ι a' ha')
  have hr : Set.range (pullback.fst i O.ι) ⊆ Set.range e := by
    rintro _ ⟨t, rfl⟩
    apply (hO _).mp
    have ht := congrArg (fun q : pullback i O.ι ⟶ Y => q t) (pullback.condition (f := i) (g := O.ι))
    simp only [Scheme.Hom.comp_apply] at ht
    change i (pullback.fst i O.ι t) ∈ O
    rw [ht]
    exact (pullback.snd i O.ι t).property
  let b := IsOpenImmersion.lift e (pullback.fst i O.ι) hr
  have hb : b ≫ e = pullback.fst i O.ι := IsOpenImmersion.lift_fac _ _ _
  refine ⟨O, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    apply (hO _).mpr
    refine ⟨l t, ?_⟩
    exact congrArg (fun q : A ⟶ D.left => q t) hl
  · rw [← hb, Category.assoc, Category.assoc]
    exact congrArg (fun q => b ≫ q)
      (congrArg (fun t => t.left) (equalizer.condition f g))

end Scheme.Hom
end AlgebraicGeometry
