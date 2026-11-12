/-
Copyright (c) 2026 Colib contributors and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionNeighborhood
public import StacksFrontier.AlgebraicGeometry.FormsTrace.FrobeniusChart

/-!
# Flatness of the original relative Frobenius of a smooth morphism

For fixed relative dimension the original Frobenius is locally the native finite free
coordinate-power map, by the actual etale chart pullback. General smooth morphisms are covered
by the original fixed-dimensional open neighborhoods. Native Frobenius naturality and stability
of open immersions under twisting identify the maps on those neighborhoods.

The fixed-dimensional proof adapts the flatness part of `syntomic_relativeFrobenius` in
StacksFrontier/AlgebraicGeometry/FormsTrace/FrobeniusLocal.lean at the pinned Stacks revision,
without importing its unrelated differential-form traces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over S)

/-- The original relative Frobenius is flat in fixed relative dimension, by the native
etale-local affine-space pullback and the full finite free coordinate-power map. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/FormsTrace/FrobeniusLocal.lean:344-352"
  "adaptation" "flatness part of the native syntomic_relativeFrobenius argument"]
theorem flat_relativeFrobenius_of_smoothOfRelativeDimension (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : Flat (relativeFrobenius S p hS X).left := by
  have : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Flat)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Flat) fun x => ?_
  obtain ⟨V, _, W, _, hxW, _, α, β, _, _, hpb⟩ :=
    exists_isPullback_relativeFrobenius_affineSpace S p hS X d x
  have H := hpb.paste_horiz (isPullback_specExpand (ULift.{u} (Fin d)) p V.toScheme)
  exact ⟨W, hxW, MorphismProperty.of_isPullback (P := @Flat) H
    (flat_specExpand (ULift.{u} (Fin d)) p (Fact.out : p.Prime).ne_zero)⟩

/-- The actual relative Frobenius of every smooth morphism is flat. No relative-dimension
certificate is required: the native standard-smooth neighborhoods supply it locally. -/
@[colib_tag "COL-1098", stacks 0FW2 "flatness conclusion, without a fixed-dimension assumption"]
theorem flat_relativeFrobenius_of_smooth [Smooth X.hom] :
    Flat (relativeFrobenius S p hS X).left := by
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  choose U hU n hn using Smooth.exists_relativeDimension_neighborhood X.hom
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat) U
    (top_le_iff.mp fun x _ => ?_) fun x => ?_
  · simpa using ⟨x, hU x⟩
  · let X₀ : Over S := Over.mk ((U x).ι ≫ X.hom)
    let i : X₀ ⟶ X := Over.homMk (U x).ι rfl
    have : SmoothOfRelativeDimension (n x) X₀.hom := hn x
    have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (U x).ι)
    have : IsOpenImmersion ((frobeniusTwist S p hS).map i).left :=
      MorphismProperty.of_isPullback (isPullback_frobeniusTwist_map S p hS i).flip
        (inferInstance : IsOpenImmersion i.left)
    have : Flat (relativeFrobenius S p hS X₀).left :=
      flat_relativeFrobenius_of_smoothOfRelativeDimension S p hS X₀ (n x)
    have heq : (U x).ι ≫ (relativeFrobenius S p hS X).left =
        (relativeFrobenius S p hS X₀).left ≫ ((frobeniusTwist S p hS).map i).left :=
      (congrArg Over.Hom.left (relativeFrobenius_naturality S p hS i)).symm
    rw [heq]
    infer_instance

end AlgebraicGeometry
