/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientTransformationComposition
public import Colib.Topology.Prespectrum.HomotopySquarePauseRight
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassSpanComposition
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassConeCompositionFaces

/-!
# Coefficient Bass Composition Charts

Constructed whole chart faces of the ORIGINAL Bass comparison-composition cube.
The inner polynomial cylinder still needs a compatible three-parameter filler.

Adapted from `CoefficientBassCompositionCharts.lean` in the original BoundedFlat development
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The exact restriction of the missing whole comparison square to a polynomial chart. -/
abbrev BoundedAboveFlatCoefficientBassCompositionChartSquare
    (i : originalPrespectrum (RingedSpace.boundedAboveFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)).toRingedSpace) ⟶
      HomotopyPushout.prespectrum
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))) :=
  (Homotopy.precomp i (boundedAboveFlatCoefficientBassComparisonHomotopy P (u ≫ v))).Square
    (Homotopy.precomp i (boundedAboveFlatCoefficientBassCompositeComparison P u v))
    (Homotopy.precomp i
      (Homotopy.precomp (boundedAboveFlatCoefficientBassSquareComparison P a)
        (boundedAboveFlatCoefficientLaurentCompositionHomotopy P u v)))
    (Homotopy.precomp i
      ((boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
        (boundedAboveFlatCoefficientBassSquareComparison P c)))

/-- The complete native plus chart is constructed from the original transposed rectangle.
Its span boundary includes exactly the terminal pause present in the fixed span homotopy. -/
def boundedAboveFlatCoefficientBassCompositionPlusChart :
    BoundedAboveFlatCoefficientBassCompositionChartSquare P u v
      (HomotopyPushout.inl
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))) := by
  refine (BoundedFlatCoefficientTransformationComposition.movingSquare P
    (underToLaurent R) u v).pauseRight |>.ofBoundaryLevels _ _ _ _ ?_ ?_ ?_ ?_
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n))
      (r, (HomotopyPushout.inl
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))).map n x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (boundedAboveFlatCoefficientBassSquareComparison P c).map n
      ((boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
        (r, (HomotopyPushout.inl
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))).map n x)) = _
    rw [boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy_inl]
    change (boundedAboveFlatCoefficientBassSquareComparison P c).map n
      (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl

/-- The separate native minus chart retains the inverse-coordinate transformation verbatim. -/
def boundedAboveFlatCoefficientBassCompositionMinusChart :
    BoundedAboveFlatCoefficientBassCompositionChartSquare P u v
      (HomotopyPushout.inr
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))) := by
  refine (BoundedFlatCoefficientTransformationComposition.movingSquare P
    (underToLaurentInvert R) u v).pauseRight |>.ofBoundaryLevels _ _ _ _ ?_ ?_ ?_ ?_
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n))
      (r, (HomotopyPushout.inr
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))).map n x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (boundedAboveFlatCoefficientBassSquareComparison P c).map n
      ((boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
        (r, (HomotopyPushout.inr
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))).map n x)) = _
    rw [boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy_inr]
    change (boundedAboveFlatCoefficientBassSquareComparison P c).map n
      (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl

end AlgebraicGeometry.Scheme.Modules
