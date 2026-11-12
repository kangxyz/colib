/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Basic
public import Colib.AlgebraicGeometry.Normalization.Compactification.FixedTarget.FiniteBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteProjectiveAmple

/-! # The actual fixed-target source geometry of an original presentation

Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/FixedTargetGeometry.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`0a419a6d3ad0d1fd1b1d9eae063fb95b6a33a5e6`. The former generic-map
normalization is replaced by the pinned native relative normalization of the
unchanged pulled étale arrow. Its finite map is followed by the fixed target
projective map. The retained target is the full original pulled overlap.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X Y A Z : Scheme.{u}}
  [IsAffine X] [IsAffine Y] [IsAffine A]
  {b : X ⟶ Spec (.of k)} {p : Y ⟶ X} [Etale p] [QuasiCompact p] [IsSeparated p]
  {a : A ⟶ X} [IsOpenImmersion a] {z : Z ⟶ X} {s : Z ⟶ Y} {x : X}
  (e : OriginalEtalePresentation k b p a z s x)

instance fixedTarget_baseNoetherian : IsNoetherianRing e.base := e.base_noetherian
instance fixedTarget_baseSmooth : Smooth e.toField := e.base_smooth
instance fixedTarget_targetAffine : IsAffine e.target := e.target_affine
instance fixedTarget_refinementOpen : IsOpenImmersion e.refinement := e.refinement_open
instance fixedTarget_compactIntegral : IsIntegral e.compact := e.compact_integral
instance fixedTarget_compactNoetherian : IsLocallyNoetherian e.compact := e.compact_noetherian
instance fixedTarget_compactNormal : IsNormal e.compact := by
  rw [isNormal_iff_stalk_normal]
  exact fun c => ⟨inferInstance, e.compact_normal c⟩
instance fixedTarget_projectiveFinite : IsFinite e.projectiveMap := e.projective_finite
instance fixedTarget_inclusionOpen : IsOpenImmersion e.inclusion := e.inclusion_open

/-- The original target's proper relative projection. -/
abbrev compactProjection :=
  e.projectiveMap ≫ (projectiveSpaceOverRing 1 e.base ↘ Spec e.base)
/-- The original relative-curve map, with unchanged coefficient ring. -/
abbrev curveProjection := e.inclusion ≫ e.compactProjection
/-- The actual original étale arrow after the presentation refinement. -/
abbrev etaleMap := pullback.snd p e.refinement
/-- The actual original puncture after the same presentation refinement. -/
abbrev punctureMap := pullback.snd a e.refinement
/-- The map whose native relative normalization supplies the source compactification. -/
abbrev sourceMap := e.etaleMap ≫ e.inclusion
/-- The actual affine overlap of the two original pullbacks. -/
abbrev originalOverlap := pullback e.etaleMap e.punctureMap

instance fixedTarget_curveSmooth : SmoothOfRelativeDimension 1 e.curveProjection :=
  e.target_smooth
instance fixedTarget_curveSeparated : IsSeparated e.curveProjection := by
  dsimp [curveProjection, compactProjection]
  infer_instance
instance fixedTarget_compactProper : IsProper e.compactProjection := by
  dsimp [compactProjection]
  infer_instance
instance fixedTarget_compactFiniteType : LocallyOfFiniteType (e.compactProjection ≫ e.toField) := by
  infer_instance

/-- Native relative normalization, including possibly disconnected étale sources. -/
abbrev sourceCompact := e.sourceMap.normalization
/-- The original affine étale source embeds openly, without replacement. -/
abbrev sourceInclusion := e.sourceMap.toNormalization
/-- The source's projective map is forced by the original target map. -/
abbrev sourceProjectiveMap := e.sourceMap.fromNormalization ≫ e.projectiveMap
/-- The same proper relative base projection on the normalized source. -/
abbrev sourceProjection :=
  e.sourceProjectiveMap ≫ (projectiveSpaceOverRing 1 e.base ↘ Spec e.base)

instance fixedTarget_sourceOpen : IsOpenImmersion e.sourceInclusion :=
  EtaleCompactification.open_normalization e.sourceMap
instance fixedTarget_sourceFinite : IsFinite e.sourceMap.fromNormalization :=
  EtaleCompactification.finite_normalization k (e.compactProjection ≫ e.toField) e.sourceMap
instance fixedTarget_sourceProjectiveFinite : IsFinite e.sourceProjectiveMap := by
  dsimp [sourceProjectiveMap]
  infer_instance
instance fixedTarget_sourceNormal : IsNormal e.sourceCompact :=
  EtaleCompactification.normal_normalization k (e.compactProjection ≫ e.toField) e.sourceMap
instance fixedTarget_sourceProper : IsProper e.sourceProjection := by
  dsimp [sourceProjection]
  infer_instance

omit [IsAffine X] [IsAffine Y] [IsAffine A] [Etale p] [IsOpenImmersion a] in
@[reassoc] theorem sourceInclusion_projection :
    e.sourceInclusion ≫ e.sourceProjection = e.etaleMap ≫ e.curveProjection := by
  simp only [sourceInclusion, sourceProjection, sourceProjectiveMap,
    ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]

/-- The retained open is the whole affine original overlap, not a parameter-open substitute. -/
abbrev retainedInclusion : e.originalOverlap ⟶ e.sourceCompact :=
  pullback.fst e.etaleMap e.punctureMap ≫ e.sourceInclusion

instance fixedTarget_retainedOpen : IsOpenImmersion e.retainedInclusion := by
  dsimp [retainedInclusion]
  infer_instance
instance fixedTarget_overlapAffine : IsAffine e.originalOverlap := by
  dsimp [originalOverlap, etaleMap, punctureMap]
  infer_instance
instance fixedTarget_retainedSmooth :
    SmoothOfRelativeDimension 1 (e.retainedInclusion ≫ e.sourceProjection) := by
  rw [retainedInclusion, Category.assoc, sourceInclusion_projection]
  have : SmoothOfRelativeDimension 1 (e.etaleMap ≫ e.curveProjection) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

/-- Only the newly added complement is reduced. The original mark is unchanged. -/
abbrev sourceInfinity := EtaleCompactification.FixedTarget.infinity e.sourceMap

/-- The closed inclusion of the whole complement of the original source in its normalization. -/
abbrev sourceInfinityInclusion :=
  EtaleCompactification.FixedTarget.infinityInclusion e.sourceMap

instance fixedTarget_infinityClosed : IsClosedImmersion e.sourceInfinityInclusion := by
  dsimp [sourceInfinityInclusion]
  infer_instance

omit [IsAffine X] [IsAffine Y] [IsAffine A] [Etale p] [QuasiCompact p]
  [IsSeparated p] [IsOpenImmersion a] in
/-- The finite chart in the presentation is Cartesian over the fixed compactification. -/
theorem goodChart_isPullback :
    IsPullback (e.etaleMap ∣_ e.goodOpen) (e.etaleMap ⁻¹ᵁ e.goodOpen).ι
      (e.goodOpen.ι ≫ e.inclusion) e.sourceMap := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · simp only [sourceMap, ← Category.assoc, morphismRestrict_ι]
  · rw [Scheme.Opens.opensRange_ι]
    ext y
    change (e.inclusion (e.etaleMap y) ∈ Set.range (e.goodOpen.ι ≫ e.inclusion)) ↔
      e.etaleMap y ∈ e.goodOpen
    constructor
    · rintro ⟨c, hc⟩
      have h := e.inclusion.isOpenEmbedding.injective hc
      exact h ▸ c.property
    · intro hy
      exact ⟨⟨e.etaleMap y, hy⟩, rfl⟩

/-- The whole new infinity is finite over the original relative coefficient base. -/
instance fixedTarget_infinityFinite :
    IsFinite (e.sourceInfinityInclusion ≫ e.sourceProjection) := by
  let : IsFinite (e.etaleMap ∣_ e.goodOpen) := e.good_finite
  let : IsFinite (e.boundaryInclusion ≫ e.compactProjection) := e.boundary_finite
  simpa only [sourceInfinityInclusion, sourceProjection, sourceProjectiveMap,
    compactProjection, Category.assoc] using
    (EtaleCompactification.FixedTarget.finite_infinity e.sourceMap e.compactProjection
      (e.goodOpen.ι ≫ e.inclusion) (e.etaleMap ⁻¹ᵁ e.goodOpen).ι
      (e.etaleMap ∣_ e.goodOpen) e.goodChart_isPullback.flip e.boundaryInclusion e.bad_cover)

instance fixedTarget_markFinite : IsFinite (e.closedInclusion ≫ e.curveProjection) :=
  e.closed_finite
instance fixedTarget_markClosed : IsClosedImmersion (e.closedLift ≫ e.sourceInclusion) := by
  let : IsClosedImmersion e.closedLift := e.closedLift_closed
  have he : e.closedLift ≫ e.sourceMap ≫ e.compactProjection =
      e.closedInclusion ≫ e.curveProjection := by
    simp only [sourceMap, curveProjection, ← Category.assoc, e.closedLift_eq]
  let : IsFinite (e.closedLift ≫ e.sourceMap ≫ e.compactProjection) := by
    rw [he]
    infer_instance
  exact EtaleCompactification.FixedTarget.marked_isClosedImmersion e.sourceMap
    e.compactProjection e.closedLift

omit [IsAffine X] [IsAffine Y] [IsAffine A] [IsOpenImmersion a] in
theorem source_disjoint_infinity :
    Disjoint (Set.range e.sourceInclusion) (Set.range e.sourceInfinityInclusion) :=
  EtaleCompactification.FixedTarget.source_disjoint_infinity e.sourceMap

omit [IsAffine X] [IsAffine Y] [IsAffine A] [IsOpenImmersion a] in
/-- Every point is in the original overlap, the full infinity, or the complete
Cartesian marked image. This is not merely a generic-fibre cover. -/
theorem retained_boundary_cover (c : e.sourceCompact) :
    c ∈ Set.range e.retainedInclusion ∨ c ∈ Set.range e.sourceInfinityInclusion ∨
      c ∈ Set.range (e.closedLift ≫ e.sourceInclusion) := by
  by_cases hc : c ∈ Set.range e.sourceInclusion
  · obtain ⟨y, rfl⟩ := hc
    rcases e.punctured_cover (e.etaleMap y) with ⟨a, ha⟩ | ⟨b, hb⟩
    · obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback e.etaleMap e.punctureMap) y a ha.symm
      exact Or.inl ⟨w, by simp only [retainedInclusion, Scheme.Hom.comp_apply, hw]⟩
    · obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
        e.closedLift_cartesian y b hb.symm
      exact Or.inr (Or.inr ⟨w, by simp only [Scheme.Hom.comp_apply, hw]⟩)
  · exact Or.inr (Or.inl (by
      change c ∈ Set.range (EtaleCompactification.FixedTarget.infinityInclusion e.sourceMap)
      rwa [EtaleCompactification.FixedTarget.range_infinityInclusion]))

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
