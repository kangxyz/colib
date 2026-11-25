/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTop
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitNative
public import Colib.KTheory.Waldhausen.Iterated.SimplexPostwhiskering
public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrumFaceEvaluation
public import Colib.KTheory.Waldhausen.Iterated.SimplexPathEmbedding

/-! Native evaluation on all three original moving pieces of the 25-node raw
Bass identity top. The two signed squares retain the original joint clock;
the middle retains the unpaused identity and the separate projection clock.
Adapted from Quillen `CoefficientPolynomialSpanUnitNodes.lean`,
`CoefficientPolynomialSpanUnitSimplex.lean` and `CoefficientPolynomialSpanUnitTop.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
  Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source
local notation "topChartMinusSimplex" => BoundedFlatCoefficientBassUnitTopCharts.minusSimplex
local notation "topChartMinusSourceIso" => BoundedFlatCoefficientBassUnitTopCharts.minusSourceIso
local notation "topChartPlusSimplex" => BoundedFlatCoefficientBassUnitTopCharts.plusSimplex
local notation "topChartPlusSourceIso" => BoundedFlatCoefficientBassUnitTopCharts.plusSourceIso
local notation "unitSquareReferences" => BoundedFlatPerfectOriginalUnitSquareSimplex.references
local notation "unitSquareSimplex" => BoundedFlatPerfectOriginalUnitSquareSimplex.simplex
local notation "unitSquareSourceMap" => BoundedFlatPerfectOriginalUnitSquareSimplex.sourceMap
local notation "unitSquareParameter" => BoundedFlatPerfectOriginalUnitSquareSimplex.squareParameter
local notation "unitSquareNative" => BoundedFlatPerfectOriginalUnitSquareSimplex.square_native
local notation "unitSquareVertices" => BoundedFlatPerfectOriginalUnitSquareSimplex.vertices
local notation "unitMiddleNative" => BoundedFlatCoefficientBassUnitTopMiddle.native

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

theorem plus_chart_family :
    topChartPlusSimplex P a = (unitSquareSimplex (polynomialProjection P a)).postcomp
      (unitSquareSourceMap (laurentPlus P a)) := by
  change ModelSimplex.ofIsos (bottomSrc P a)
    (fun i ↦ unitSquareVertices (polynomialProjection P a) i ≫
      unitSquareSourceMap (laurentPlus P a))
    (fun i ↦ topChartPlusSourceIso P a ≪≫ isoWhiskerRight
      (unitSquareReferences (polynomialProjection P a) i)
      (unitSquareSourceMap (laurentPlus P a)).hom.toFunctor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_postcomp _ _ _ _).symm

/-- The square parameter on the positive chart of the coefficient unit. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  (embed plusFace).comp unitSquareParameter

theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (plusParameter (r, s), x) =
      ((boundedAboveFlatCoefficientPolynomialIdentitySquare P a).postcompose
        (K (laurentPlus P a))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_face (simplex P a) plusFace n
    (unitSquareParameter (r, s)) x).trans ?_
  rw [plus_face, plus_chart_family]
  refine (prespectrumSimplexFamily_postcomp (unitSquareSimplex (polynomialProjection P a))
    (unitSquareSourceMap (laurentPlus P a)) n (unitSquareParameter (r, s)) x).trans ?_
  exact congrArg ((K (laurentPlus P a)).map n)
    (unitSquareNative (polynomialProjection P a) n r s x)

theorem minus_chart_family :
    topChartMinusSimplex P a = (unitSquareSimplex (polynomialProjection P a)).postcomp
      (unitSquareSourceMap (laurentMinus P a)) := by
  change ModelSimplex.ofIsos (bottomSrc P a)
    (fun i ↦ unitSquareVertices (polynomialProjection P a) i ≫
      unitSquareSourceMap (laurentMinus P a))
    (fun i ↦ topChartMinusSourceIso P a ≪≫ isoWhiskerRight
      (unitSquareReferences (polynomialProjection P a) i)
      (unitSquareSourceMap (laurentMinus P a)).hom.toFunctor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_postcomp _ _ _ _).symm

/-- The square parameter on the negative chart of the coefficient unit. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  (embed minusFace).comp unitSquareParameter

theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (minusParameter (r, s), x) =
      ((boundedAboveFlatCoefficientPolynomialIdentitySquare P a).postcompose
        (K (laurentMinus P a))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_face (simplex P a) minusFace n
    (unitSquareParameter (r, s)) x).trans ?_
  rw [minus_face, minus_chart_family]
  refine (prespectrumSimplexFamily_postcomp (unitSquareSimplex (polynomialProjection P a))
    (unitSquareSourceMap (laurentMinus P a)) n (unitSquareParameter (r, s)) x).trans ?_
  exact congrArg ((K (laurentMinus P a)).map n)
    (unitSquareNative (polynomialProjection P a) n r s x)


/-- The parameter for the overlap face of the coefficient unit. -/
def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  (embed middleFace).comp BoundedFlatCoefficientBassUnitTopMiddle.parameter.{u}

theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (middleParameter.{u} (r, s), x) =
      (boundedAboveFlatCoefficientBassSquareComparison P a).map n
        (HomotopyPushout.cylinder (K (polynomialProjection P a)) (K (polynomialProjection P a)) n
          (s, (boundedAboveFlatCoefficientIdentityHomotopy P a).level n (r, x))) := by
  refine (prespectrumSimplexFamily_face (simplex P a) middleFace n
    (BoundedFlatCoefficientBassUnitTopMiddle.parameter.{u} (r, s)) x).trans ?_
  rw [middle_face]
  exact unitMiddleNative P a n r s x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop
