/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartCompactificationGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The genuine retained open inside the original chart compactification

The existing explicit lift is Cartesian over the original inclusion j.
Openness, relative smooth dimension and affineness are transported on these
same schemes. Neither sections nor the marked refinement are replaced.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart
variable {A Y Z U N : Scheme.{u}}
  (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z)
  (f : U ⟶ Y) (j : U ⟶ N) (fN : N ⟶ Y) (hj : j ≫ fN = f)

/-- The retained lift is precisely the actual base change of the old inclusion. -/
theorem retainedToCompactification_isPullback :
    IsPullback (retainedToCompactification q p s f j fN hj)
      (pullback.snd (original q p s ≫ (q ≫ p)) f)
      (pullback.snd (original q p s ≫ (q ≫ p)) fN) j := by
  refine IsPullback.of_right
    (h₁₂ := pullback.fst (original q p s ≫ (q ≫ p)) fN)
    (h₂₂ := fN) (v₁₃ := original q p s ≫ (q ≫ p)) ?_
    (retainedToCompactification_snd q p s f j fN hj)
    (IsPullback.of_hasPullback (original q p s ≫ (q ≫ p)) fN)
  simpa only [retainedToCompactification_fst, hj] using
    (IsPullback.of_hasPullback (original q p s ≫ (q ≫ p)) f)

/-- The original retained open remains an open immersion after the chart refinement. -/
instance retainedToCompactification_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (retainedToCompactification q p s f j fN hj) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (retainedToCompactification_isPullback q p s f j fN hj).flip inferInstance

/-- The actual retained curve has the original relative smooth dimension. -/
theorem curve_projection_smoothOfRelativeDimension (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    SmoothOfRelativeDimension d (pullback.fst (original q p s ≫ (q ≫ p)) f) :=
  inferInstance

/-- The retained inclusion followed by the compactified structure map is smooth. -/
theorem retainedToCompactification_structure_smoothOfRelativeDimension (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    SmoothOfRelativeDimension d
      (retainedToCompactification q p s f j fN hj ≫
        pullback.fst (original q p s ≫ (q ≫ p)) fN) := by
  rw [retainedToCompactification_fst]
  exact curve_projection_smoothOfRelativeDimension q p s f d

/-- An affine original curve morphism over the affine chart refinement has the
same affine retained pullback. No affineness of the compactification is required. -/
theorem curve_isAffine_of_isAffineHom
    [IsAffine (refinement q p s)] [IsAffineHom f] :
    IsAffine (curve q p s f) :=
  isAffine_of_isAffineHom (pullback.fst (original q p s ≫ (q ≫ p)) f)

/-- In particular, affine original chart, section base and retained source give
an affine actual retained curve. -/
theorem curve_isAffine_of_affine_chart
    [IsAffine A] [IsAffine Y] [IsAffine Z] [IsAffine U] :
    IsAffine (curve q p s f) := by
  let : IsAffineHom f := @isAffineHom_of_isAffine U Y f inferInstance inferInstance
  exact curve_isAffine_of_isAffineHom q p s f

end AlgebraicGeometry.Scheme.EtaleChart
