/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.RetainedOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedSmoothSites
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare

/-! # The actual first correction square and its unchanged original maps

The two covering sources are pulled back along the same U/intersection/V open.
The retained overlap target is restricted only by V. Every comparison below is
an equation of actual scheme or smooth-site maps, before applying a presheaf.
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

local instance : IsAffine e.target := e.target_affine

instance originalEtaleRefinement_affine : IsAffine (pullback p.left e.refinement) :=
  isAffine_of_isAffineHom (pullback.snd p.left e.refinement)

instance originalPunctureRefinement_affine : IsAffine (pullback a.left e.refinement) :=
  isAffine_of_isAffineHom (pullback.snd a.left e.refinement)

variable (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme] [hAffine : IsAffine (parameterOpen e.curveProjection U V).toScheme]

/-- The literal first refined source with its original field structure. -/
abbrev retainedEtaleSite : SmoothSite (Spec (.of k)) :=
  letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
  refinedFirstSite e.toField q U V π j p' hq
/-- The literal simultaneously refined puncture. -/
abbrev retainedPunctureSite : SmoothSite (Spec (.of k)) :=
  letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
  refinedSecondSite e.toField q U V a'
/-- The exact scheme pullback of the two sources. -/
abbrev retainedOverlapSite : SmoothSite (Spec (.of k)) :=
  letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
  refinedOverlapSite e.toField q U V π j p' hq a'

local instance : Smooth (parameterProjection q U V) :=
  SmoothOfRelativeDimension.smooth 1 _

/-- The ambient first correction is the retained original parameter open. -/
abbrev retainedAmbientSite : SmoothSite (Spec (.of k)) :=
  letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
  letI : QuasiCompact (parameterProjection q U V ≫ V.ι ≫ e.toField) :=
    quasiCompact_of_compactSpace _
  SmoothSite.mk (parameterProjection q U V ≫ V.ι ≫ e.toField)

/-- The original étale arrow pulled back along the common parameter inclusion. -/
def retainedEtaleArrow : retainedEtaleSite p a z s x e U V ⟶
    retainedAmbientSite p a z s x e U V :=
  SmoothSite.homMk (firstMap q U V p') (by
    change firstMap q U V p' ≫ parameterProjection q U V ≫ V.ι ≫ e.toField =
      (firstInclusion q U V π j p' hq ≫ compactificationProjection π V) ≫ (V.ι ≫ e.toField)
    rw [firstInclusion_projection, Category.assoc])

/-- The original puncture pulled back along exactly the same inclusion. -/
def retainedPunctureArrow : retainedPunctureSite p a z s x e U V ⟶
    retainedAmbientSite p a z s x e U V :=
  SmoothSite.homMk (secondMap q U V a') (by rfl)

/-- The first correction is the actual Cartesian smooth-site square. -/
def retainedCorrectionSquare : Square (SmoothSite (Spec (.of k))) :=
  letI : IsAffine (parameterOpen e.curveProjection U V).toScheme := hAffine
  ⟨refinedBeta e.toField q U V π j p' hq a',
    refinedAlpha e.toField q U V π j p' hq a',
    retainedPunctureArrow p a z s x e U V,
    retainedEtaleArrow p a z s x e U V, by
      apply MorphismProperty.Over.Hom.ext
      exact pullback.condition.symm⟩

instance retainedCorrectionSquare_etale :
    Etale (retainedCorrectionSquare p a z s x e U V).f₃₄.left := by
  change Etale (firstMap q U V p')
  infer_instance

/-- Cartesian before applying any presheaf or forgetting any nilpotents. -/
theorem retainedCorrectionSquare_isPullback :
    (retainedCorrectionSquare p a z s x e U V).IsPullback := by
  apply IsPullback.of_map_of_faithful (SmoothSite.forgetScheme (Spec (.of k)))
  exact (IsPullback.of_hasPullback (firstMap q U V p') (secondMap q U V a')).flip

/-- Map from the unchanged presentation overlap to the unchanged original overlap. -/
def overlapToOriginalScheme : e.originalOverlap ⟶ pullback p.left a.left :=
  pullback.map _ _ _ _ (pullback.fst p.left e.refinement)
    (pullback.fst a.left e.refinement) e.refinement
    (pullback.condition (f := p.left) (g := e.refinement)).symm
    (pullback.condition (f := a.left) (g := e.refinement)).symm

omit [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left] [Etale p.left]
  [IsOpenImmersion a.left] in
/-- The exact overlap map retains the original first projection. -/
@[reassoc (attr := simp)] theorem overlapToOriginalScheme_fst :
    overlapToOriginalScheme p a z s x e ≫ pullback.fst p.left a.left =
      pullback.fst p' a' ≫ pullback.fst p.left e.refinement := by
  simp [overlapToOriginalScheme, pullback.map]

omit [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left] [Etale p.left]
  [IsOpenImmersion a.left] in
@[reassoc (attr := simp)] theorem overlapToOriginalScheme_snd :
    overlapToOriginalScheme p a z s x e ≫ pullback.snd p.left a.left =
      pullback.snd p' a' ≫ pullback.fst a.left e.refinement := by
  simp [overlapToOriginalScheme, pullback.map]

omit [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left] [Etale p.left]
  [IsOpenImmersion a.left] in
/-- The overlap comparison preserves the literal original field structure. -/
@[reassoc] theorem overlapToOriginalScheme_over :
    overlapToOriginalScheme p a z s x e ≫ (pullback.snd p.left a.left ≫ A.hom) =
      (e.retainedInclusion ≫ π) ≫ e.toField := by
  calc
    _ = pullback.snd p' a' ≫ pullback.fst a.left e.refinement ≫ A.hom := by
      exact overlapToOriginalScheme_snd_assoc p a z s x e A.hom
    _ = pullback.snd p' a' ≫ a' ≫ e.refinement ≫ X.hom := by
      rw [← MorphismProperty.Over.w a, pullback.condition_assoc]
    _ = pullback.fst p' a' ≫ p' ≫ q ≫ e.toField := by
      rw [pullback.condition_assoc, e.base_compatibility]
      all_goals rfl
    _ = _ := by
      change pullback.fst p' a' ≫ p' ≫ q ≫ e.toField =
        ((pullback.fst p' a' ≫ j) ≫ π) ≫ e.toField
      simp only [Category.assoc, sourceInclusion_projection_assoc]

/-- The retained étale source still maps to the original source Y. -/
def retainedEtaleToOriginal : (retainedCorrectionSquare p a z s x e U V).X₃ ⟶ Y :=
  SmoothSite.homMk
    (pullback.fst p' (parameterOpen q U V).ι ≫ pullback.fst p.left e.refinement) (by
      change (pullback.fst p' _ ≫ pullback.fst p.left e.refinement) ≫ Y.hom =
        (firstInclusion q U V π j p' hq ≫ compactificationProjection π V) ≫
          (V.ι ≫ e.toField)
      simp only [Category.assoc, compactificationProjection, morphismRestrict_ι_assoc,
        firstInclusion_original_assoc, sourceInclusion_projection_assoc]
      rw [← MorphismProperty.Over.w p, pullback.condition_assoc, e.base_compatibility])

/-- The actual original overlap restriction used by the first correction. -/
def retainedOverlapToOriginal : (retainedCorrectionSquare p a z s x e U V).X₁ ⟶
    SmoothSite.etalePullback p a :=
  SmoothSite.homMk
    (RelativeCurvePencil.RelativeBase.overlapToOriginal q U V p' a' ≫
      overlapToOriginalScheme p a z s x e) (by
      change (RelativeCurvePencil.RelativeBase.overlapToOriginal q U V p' a' ≫
        overlapToOriginalScheme p a z s x e) ≫
          (pullback.snd p.left a.left ≫ A.hom) = _
      rw [Category.assoc, overlapToOriginalScheme_over]
      simp only [retainedInclusion, Category.assoc,
        RelativeCurvePencil.RelativeBase.overlapToOriginal_fst_assoc]
      change pullback.fst _ _ ≫ pullback.fst p' (parameterOpen q U V).ι ≫
          j ≫ π ≫ e.toField =
        (pullback.fst _ _ ≫ firstInclusion q U V π j p' hq ≫
          compactificationProjection π V) ≫ (V.ι ≫ e.toField)
      simp only [Category.assoc, compactificationProjection, morphismRestrict_ι_assoc,
        firstInclusion_original_assoc])

/-- The first correction retains exactly the original étale projection. -/
@[reassoc] theorem retainedOverlapToOriginal_etale :
    retainedOverlapToOriginal p a z s x e U V ≫ SmoothSite.etalePullbackFst p a =
      (retainedCorrectionSquare p a z s x e U V).f₁₃ ≫
        retainedEtaleToOriginal p a z s x e U V := by
  apply MorphismProperty.Over.Hom.ext
  change (RelativeCurvePencil.RelativeBase.overlapToOriginal q U V p' a' ≫
    overlapToOriginalScheme p a z s x e) ≫ pullback.fst p.left a.left =
      pullback.fst (firstMap q U V p') (secondMap q U V a') ≫
        (pullback.fst p' (parameterOpen q U V).ι ≫ pullback.fst p.left e.refinement)
  calc
    _ = RelativeCurvePencil.RelativeBase.overlapToOriginal q U V p' a' ≫
        (overlapToOriginalScheme p a z s x e ≫ pullback.fst p.left a.left) :=
      Category.assoc _ _ _
    _ = RelativeCurvePencil.RelativeBase.overlapToOriginal q U V p' a' ≫
        (pullback.fst p' a' ≫ pullback.fst p.left e.refinement) :=
      congrArg (RelativeCurvePencil.RelativeBase.overlapToOriginal q U V p' a' ≫ ·)
        (overlapToOriginalScheme_fst p a z s x e)
    _ = _ := by
      rw [← Category.assoc, RelativeCurvePencil.RelativeBase.overlapToOriginal_fst,
        Category.assoc]

/-- The retained first source is the literal original-source pullback. -/
theorem retainedEtale_original_isPullback :
    IsPullback (retainedCorrectionSquare p a z s x e U V).f₃₄.left
      (retainedEtaleToOriginal p a z s x e U V).left
      (retainedToOriginal e U V) p.left := by
  exact (IsPullback.of_hasPullback p' (parameterOpen q U V).ι).flip.paste_vert
    (IsPullback.of_hasPullback p.left e.refinement).flip

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
