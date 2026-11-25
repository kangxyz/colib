/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumTripleSimplex
public import Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentProductNaturality

/-!
# One actual geometric reference for both polynomial-overlap charts

Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassOverlapReference.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOverlap
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NE" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "NZ" => boundedAboveFlatPerfectNormalizedPullback_obj_zero
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The exact model morphism inducing the original polynomial-projection prespectrum map. -/
def projectionMap : asSmallCategory (W (space (op P, a))) ⟶
    asSmallCategory (W
      (space (op P, (polynomialUnderFunctor R).obj a))) :=
  asSmallCategoryMap _ _ (NE (polynomialProjection P a))
    (NZ _)

theorem projectionMap_prespectrum : prespectrumMap (projectionMap P (a := a)) =
    boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a) := rfl

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The actual reference of the chart's already accepted merged 17-simplex. -/
def chartReference := BoundedFlatPerfectTripleSimplex.source
  (coefficientMap P (α.app c))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((polynomialUnderFunctor R).map u))

/-- The overlap reference uses only the common Laurent projection and the two coefficient maps. -/
def commonReference : asSmallCategory (W (space (op P, a))) ⟶
    asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj c))) :=
  asSmallCategoryMap _ _ (NE
    (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u))
    (NZ _)

/-- Polynomial naturality and the actual chart projection equation identify the geometric total. -/
theorem chart_total
    (hα : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (coefficientMap P (α.app c) ≫
      coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      coefficientMap P ((polynomialUnderFunctor R).map u)) ≫ polynomialProjection P a =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have hu := polynomialProjection_naturality P u
  have hv := polynomialProjection_naturality P v
  simp only [Category.assoc]
  rw [hu, ← Category.assoc _ _ (coefficientMap P u), hv]
  simp only [Category.assoc]
  rw [← Category.assoc (coefficientMap P (α.app c)) (polynomialProjection P c), hα]

/-- An actual normalized pullback composition iso, after the literal geometric total equality. -/
def commonToChartReference
    (hα : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (commonReference P u v).hom.toFunctor ≅
      (projectionMap P (a := a) ≫ chartReference P u v α).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg N (chart_total P u v α hα).symm) ≪≫
      NC
        (coefficientMap P (α.app c) ≫
          coefficientMap P ((polynomialUnderFunctor R).map v) ≫
          coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)) AsSmall.up)

/-- The positive chart supplies its original geometric projection equation. -/
def plusReference := commonToChartReference P u v (underToLaurent R)
  (laurentPlus_projection P c)

/-- The negative chart supplies its distinct original geometric projection equation. -/
def minusReference := commonToChartReference P u v (underToLaurentInvert R)
  (laurentMinus_projection P c)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOverlap
