/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic

/-!
# Actual isomorphisms of entire finite-flat spans

An isomorphism preserving both actual span legs preserves the existing
correspondence, by native finite-pushforward functoriality and the genuine
fundamental-cycle isomorphism theorem. No reduction is applied.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {D E : Scheme.{u}}

/-- Both actual span maps, not merely the supports, identify the entire correspondence. -/
theorem ofFiniteFlatSpan_eq_of_iso (e : D ≅ E)
    (f : D ⟶ X.left) [IsFinite f] [Flat f]
    (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom)
    (f' : E ⟶ X.left) [IsFinite f'] [Flat f']
    (g' : E ⟶ Y.left) (h' : f' ≫ X.hom = g' ≫ Y.hom)
    (hf : e.hom ≫ f' = f) (hg : e.hom ≫ g' = g) :
    ofFiniteFlatSpan f g h = ofFiniteFlatSpan f' g' h' := by
  haveI := isNoetherian_of_finiteType f
  haveI := isNoetherian_of_finiteType f'
  haveI := isFinite_spanMap f g h
  haveI := isFinite_spanMap f' g' h'
  have he : e.hom ≫ pullback.lift f' g' h' = pullback.lift f g h := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using hf
    · simpa only [Category.assoc, pullback.lift_snd] using hg
  apply Subtype.ext
  rw [ofFiniteFlatSpan_val, ofFiniteFlatSpan_val,
    ← finiteCyclePushforward_fundamentalCycle_iso e,
    finiteCyclePushforward_comp_apply, he]

end AlgebraicGeometry.Cor
