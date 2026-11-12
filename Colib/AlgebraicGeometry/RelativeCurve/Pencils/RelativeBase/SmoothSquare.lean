/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedSmoothSites
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Mathlib.CategoryTheory.Square

/-! # The smooth-site square on the actual relative pencil refinement -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {k : Type u} [Field k] {S C : Scheme.{u}}
  {X Y A : SmoothSite (Spec (.of k))}
  [IsAffine S] [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X.left ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q] (ht : q ≫ t = X.hom)
  (p : Y ⟶ X) [Etale p.left] (a : A ⟶ X) [IsOpenImmersion a.left]
  (π : C ⟶ S) (j : Y.left ⟶ C) [IsOpenImmersion j] (hq : j ≫ π = p.left ≫ q)
  (U : X.left.Opens) (V : S.Opens)
  [IsAffine V.toScheme] [IsAffine (parameterOpen q U V).toScheme]

local notation "W" => parameterOpen q U V
set_option quotPrecheck false in
local notation "Q" => (SmoothSite.opensFunctor X).obj W
local notation "Y'" => refinedFirstSite t q U V π j p.left hq
local notation "A'" => refinedSecondSite t q U V a.left

omit [IsAffine S] [IsAffine X.left] [Smooth t] [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] [IsAffine V.toScheme]
  [IsAffine (parameterOpen q U V).toScheme] in
include ht in
private theorem parameter_base_map :
    parameterProjection q U V ≫ V.ι ≫ t = (W).ι ≫ X.hom := by
  rw [← Category.assoc, parameterProjection_base, Category.assoc, ht]

/-- The first refined leg has the actual original base projection. -/
def firstParameterArrow : Y' ⟶ Q :=
  SmoothSite.homMk (firstMap q U V p.left) (by
    change firstMap q U V p.left ≫ (W).ι ≫ X.hom =
      (firstInclusion q U V π j p.left hq ≫ compactificationProjection π V) ≫ V.ι ≫ t
    rw [firstInclusion_projection, Category.assoc, parameter_base_map t q ht U V])

/-- The independent second refined leg has the same parameter. -/
def secondParameterArrow : A' ⟶ Q :=
  SmoothSite.homMk (secondMap q U V a.left) (by
    change secondMap q U V a.left ≫ (W).ι ≫ X.hom =
      (secondMap q U V a.left ≫ parameterProjection q U V) ≫ V.ι ≫ t
    rw [Category.assoc, parameter_base_map t q ht U V])

/-- The original square uses the original étale and open legs. -/
def originalSmoothSquare : Square (SmoothSite (Spec (.of k))) where
  f₁₂ := SmoothSite.etalePullbackSnd p a
  f₁₃ := SmoothSite.etalePullbackFst p a
  f₂₄ := a
  f₃₄ := p
  fac := (SmoothSite.etalePullbackCone p a).condition.symm

omit [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left] [IsOpenImmersion a.left] in
theorem originalSmoothSquare_isPullback : (originalSmoothSquare p a).IsPullback :=
  (IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit p a)).flip

/-- The exact refined square used by the signed pencil. -/
def refinedSmoothSquare : Square (SmoothSite (Spec (.of k))) where
  f₁₂ := refinedBeta t q U V π j p.left hq a.left
  f₁₃ := refinedAlpha t q U V π j p.left hq a.left
  f₂₄ := secondParameterArrow t q ht a U V
  f₃₄ := firstParameterArrow t q ht p π j hq U V
  fac := MorphismProperty.Over.Hom.ext (refinedOverlap_square q U V p.left a.left).symm

omit [IsOpenImmersion j] in
theorem refinedSmoothSquare_isPullback :
    (refinedSmoothSquare t q ht p a π j hq U V).IsPullback :=
  IsPullback.of_map_of_faithful (SmoothSite.forgetScheme (Spec (.of k)))
    ((IsPullback.of_hasPullback (firstMap q U V p.left) (secondMap q U V a.left)).flip)

/-- Every arrow of the comparison uses the original source restriction. -/
def refinedSmoothSquareMap :
    refinedSmoothSquare t q ht p a π j hq U V ⟶ originalSmoothSquare p a where
  τ₄ := SmoothSite.openInclusion X W
  τ₂ := SmoothSite.homMk (pullback.fst a.left (W).ι) (by
    change pullback.fst a.left (W).ι ≫ A.hom =
      (secondMap q U V a.left ≫ parameterProjection q U V) ≫ V.ι ≫ t
    rw [Category.assoc, parameter_base_map t q ht U V, ← Category.assoc,
      ← pullback.condition, Category.assoc, MorphismProperty.Over.w])
  τ₃ := SmoothSite.homMk (pullback.fst p.left (W).ι) (by
    change pullback.fst p.left (W).ι ≫ Y.hom =
      (firstInclusion q U V π j p.left hq ≫ compactificationProjection π V) ≫ V.ι ≫ t
    rw [firstInclusion_projection, Category.assoc, parameter_base_map t q ht U V,
      ← Category.assoc, ← pullback.condition, Category.assoc, MorphismProperty.Over.w])
  τ₁ := SmoothSite.homMk (overlapToOriginal q U V p.left a.left) (by
    have hOrig : pullback.snd p.left a.left ≫ A.hom = pullback.fst p.left a.left ≫ Y.hom := by
      rw [← MorphismProperty.Over.w a, ← MorphismProperty.Over.w p]
      exact (pullback.condition_assoc (f := p.left) (g := a.left) X.hom).symm
    have hFirst : pullback.fst p.left (W).ι ≫ Y.hom =
        (firstInclusion q U V π j p.left hq ≫ compactificationProjection π V) ≫ V.ι ≫ t := by
      rw [firstInclusion_projection, Category.assoc, parameter_base_map t q ht U V,
        ← Category.assoc, ← pullback.condition, Category.assoc, MorphismProperty.Over.w]
    change overlapToOriginal q U V p.left a.left ≫ (pullback.snd p.left a.left ≫ A.hom) =
      commonProjection (compactificationProjection π V) (firstInclusion q U V π j p.left hq)
        (pullback.fst _ _) ≫ V.ι ≫ t
    rw [hOrig, overlapToOriginal_fst_assoc, hFirst]
    simp only [commonProjection, Category.assoc])
  comm₁₂ := MorphismProperty.Over.Hom.ext (overlapToOriginal_snd q U V p.left a.left).symm
  comm₁₃ := MorphismProperty.Over.Hom.ext (overlapToOriginal_fst q U V p.left a.left).symm
  comm₂₄ := MorphismProperty.Over.Hom.ext pullback.condition.symm
  comm₃₄ := MorphismProperty.Over.Hom.ext pullback.condition.symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
