/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.BoundaryNeighborhood
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# The missing boundary of the retained target

The finite bad boundary bounds the fibres of the closed complement of the
retained target. Properness then gives finiteness of that closed complement.

Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Presentation/MissingBoundary.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `7ca0892f16a7e832ef069d9f781edbdf321748d6`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X Y A Z : Scheme.{u}}
  {b : X ⟶ Spec (.of k)} {p : Y ⟶ X} {a : A ⟶ X} {z : Z ⟶ X}
  {s : Z ⟶ Y} {x : X} (e : OriginalEtalePresentation k b p a z s x)

local instance : IsOpenImmersion e.inclusion := e.inclusion_open

/-- The closed complement of the actual retained target. -/
abbrev missing := retainedBoundary e.inclusion.opensRange

/-- The closed complement inclusion into the compactification. -/
abbrev missingInclusion : e.missing ⟶ e.compact :=
  retainedBoundaryInclusion e.inclusion.opensRange

/-- The support of the missing boundary is precisely the complement of the target. -/
theorem missing_range : Set.range e.missingInclusion = (Set.range e.inclusion)ᶜ := by
  simpa only [Scheme.Hom.coe_opensRange] using
    range_retainedBoundaryInclusion e.inclusion.opensRange

/-- The missing boundary of the retained target is finite over the presentation base. -/
theorem missing_finite : IsFinite
    (e.missingInclusion ≫ e.projectiveMap ≫ (projectiveSpaceOverRing 1 e.base ↘ Spec e.base)) := by
  let q := e.projectiveMap ≫ (projectiveSpaceOverRing 1 e.base ↘ Spec e.base)
  have : IsFinite e.projectiveMap := e.projective_finite
  have : IsFinite (e.boundaryInclusion ≫ q) := e.boundary_finite
  have : IsProper q := by dsimp [q]; infer_instance
  have : IsProper (e.missingInclusion ≫ q) := inferInstance
  have hf : ∀ y, ((e.missingInclusion ≫ q) ⁻¹' {y}).Finite := by
    intro y
    have hD := ((e.boundaryInclusion ≫ q).finite_preimage_singleton y).image e.boundaryInclusion
    apply (hD.preimage e.missingInclusion.isClosedEmbedding.injective.injOn).subset
    intro w hw
    have hn : e.missingInclusion w ∉ Set.range e.inclusion := by
      change e.missingInclusion w ∈ (Set.range e.inclusion)ᶜ
      rw [← e.missing_range]
      exact ⟨w, rfl⟩
    have hbad : e.missingInclusion w ∉ Set.range (e.goodOpen.ι ≫ e.inclusion) := by
      rintro ⟨v, hv⟩
      exact hn ⟨e.goodOpen.ι v, hv⟩
    obtain ⟨v, hv⟩ := e.bad_cover hbad
    refine ⟨v, ?_, hv⟩
    change q (e.boundaryInclusion v) = y
    change q (e.missingInclusion w) = y at hw
    simpa only [hv] using hw
  have : LocallyQuasiFinite (e.missingInclusion ≫ q) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ hf
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
