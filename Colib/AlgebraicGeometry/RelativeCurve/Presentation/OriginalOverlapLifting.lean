/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.CorrectionSquare
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteProjectiveProducer
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Restriction

/-! # The first genuine signed correction of the original overlap section

The native finite normalization, full finite infinity, retained affine overlap,
whole marked Cartesian scheme and all compactification maps are constructed
from the original presentation. The relative producer then constructs the
common U/V neighborhood, frames, both Serre pairs and signed family. Finally
only an original section is restricted along the literal original overlap map.
No lifting, compactification or section-existence provider is assumed.

Original correspondence: FixedTarget/NormalizedLifting, blob
`5065ffdd86e55eacdc74bffd8b15745f6eb6a3f7`; FixedTarget/OriginalOverlapLifting,
`7f412e754d8c7029795af6ed5cecbe82ca51de7f`; Original/OverlapSectionLifting,
`85e04ac56874c18c57fc267d9abcccea310e9912`; Presentation/OverlapLifting,
`f7c8770fb4336ef73bd86448c61e9f75d54834fc`, all at motivic commit
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/
@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X Y A : SmoothSite (Spec (.of k))}
  [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left]
  (p : Y ⟶ X) [Etale p.left] (a : A ⟶ X) [IsOpenImmersion a.left]
  {Z : Scheme.{u}} (z : Z ⟶ X.left) (s : Z ⟶ Y.left) (x : X.left)
  (e : OriginalEtalePresentation k X.hom p.left a.left z s x)

local notation "q" => e.curveProjection
local notation "π" => e.sourceProjection
local notation "j" => e.sourceInclusion
local notation "p'" => e.etaleMap
local notation "a'" => e.punctureMap
local notation "hq" => e.sourceInclusion_projection
local notation "v" => e.retainedInclusion

local instance : IsAffine e.target := e.target_affine

local instance : IsAffine e.originalOverlap := by
  change IsAffine (pullback p' a')
  let : IsAffineHom p' := isAffineHom_of_isAffine p'
  exact isAffine_of_isAffineHom (pullback.snd p' a')

section Restriction
variable (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme] [hAffine : IsAffine (parameterOpen e.curveProjection U V).toScheme]

/-- The entire retained overlap over V restricts the original overlap. There is
no U restriction on this coefficient target. -/
def retainedTargetToOriginal : refinedTargetSite e.toField V π v ⟶
    SmoothSite.etalePullback p a :=
  SmoothSite.homMk
    ((sourceBaseOpen π V v).ι ≫ overlapToOriginalScheme p a z s x e) (by
      change ((sourceBaseOpen π V v).ι ≫ overlapToOriginalScheme p a z s x e) ≫
        (pullback.snd p.left a.left ≫ A.hom) =
        (sourceBaseMap π V v ≫ compactificationProjection π V) ≫ (V.ι ≫ e.toField)
      rw [Category.assoc, overlapToOriginalScheme_over, sourceBaseMap_projection,
        morphismRestrict_ι_assoc])

/-- The pencil graph followed by the retained-target restriction is exactly the
original overlap arrow, with no replacement of its coefficient section. -/
@[reassoc] theorem refinedGraph_retainedTargetToOriginal :
    letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
    refinedGraph e.toField q U V π j p' hq a' v (𝟙 _) (Category.id_comp _) ≫
        retainedTargetToOriginal p a z s x e V =
      retainedOverlapToOriginal p a z s x e U V := by
  apply MorphismProperty.Over.Hom.ext
  change refinedTargetMap q U V π j p' hq a' v (𝟙 _) (Category.id_comp _) ≫
      ((sourceBaseOpen π V v).ι ≫ overlapToOriginalScheme p a z s x e) = _
  simp only [← Category.assoc, refinedTargetMap_original, Category.comp_id]
  all_goals rfl

/-- A constructed normalized pencil lifts restrictions of the exact original
sections, with the original beta-minus-alpha sign. -/
theorem originalOverlap_hasRestrictionDifferenceLifting
    (P : PresheafWithTransfers.{u + 1} k)
    (hL : letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
      P.HasRestrictionDifferenceLifting
      (refinedGraph e.toField q U V π j p' hq a' v (𝟙 _) (Category.id_comp _))
      (refinedBeta e.toField q U V π j p' hq a')
      (refinedAlpha e.toField q U V π j p' hq a')) :
    letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
    P.HasRestrictionDifferenceLifting (retainedOverlapToOriginal p a z s x e U V)
      (retainedCorrectionSquare p a z s x e U V).f₁₂
      (retainedCorrectionSquare p a z s x e U V).f₁₃ := by
  have h := PresheafWithTransfers.HasRestrictionDifferenceLifting.restrict P hL
    (retainedTargetToOriginal p a z s x e V)
  rw [refinedGraph_retainedTargetToOriginal] at h
  exact h
end Restriction

/-- The actual first original correction. Both source opens use the same
simultaneous refinement; every point of the full marked scheme over V remains
in U. The conclusion concerns restrictions of the original overlap sections. -/
theorem exists_original_overlap_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ U : e.target.Opens, IsAffineOpen U ∧ e.point ∈ U ∧
      ∃ (V : (Spec e.base).Opens) (hV : IsAffineOpen V),
        q e.point ∈ V ∧
        (∀ c : e.closed, (e.closedInclusion ≫ q) c ∈ V → e.closedInclusion c ∈ U) ∧
        ∃ hW : IsAffineOpen (parameterOpen q U V),
          letI : IsAffine V.toScheme := hV
          letI : IsAffine (parameterOpen q U V).toScheme := hW
          P.HasRestrictionDifferenceLifting (retainedOverlapToOriginal p a z s x e U V)
            (retainedCorrectionSquare p a z s x e U V).f₁₂
            (retainedCorrectionSquare p a z s x e U V).f₁₃ := by
  let : IsFinite (e.sourceInfinityInclusion ≫ e.sourceProjectiveMap ≫
      (projectiveSpaceOverRing 1 e.base ↘ Spec e.base)) :=
    inferInstanceAs (IsFinite (e.sourceInfinityInclusion ≫ e.sourceProjection))
  let : SmoothOfRelativeDimension 1 (e.retainedInclusion ≫ e.sourceProjectiveMap ≫
      (projectiveSpaceOverRing 1 e.base ↘ Spec e.base)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (e.retainedInclusion ≫ e.sourceProjection))
  obtain ⟨U, hU, hxU, V, hV, hxV, hmark, hW, hL⟩ :=
    exists_refined_finiteProjective_lifting e.base 1 e.toField q
      e.sourceProjectiveMap j p' hq a' e.closedInclusion e.closedLift
      e.closedLift_eq e.closedLift_cartesian e.sourceInfinityInclusion
      e.source_disjoint_infinity e.punctured_disjoint v e.retained_boundary_cover
      (𝟙 _) (Category.id_comp _) e.point P hP
  let : IsAffine V.toScheme := hV
  let : IsAffine (parameterOpen q U V).toScheme := hW
  exact ⟨U, hU, hxU, V, hV, hxV, hmark, hW,
    originalOverlap_hasRestrictionDifferenceLifting p a z s x e U V P hL⟩

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
