/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionRectangleParameters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareOriginalRectangle
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassChartPasting
public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrumFaceEvaluation

/-!
# Geometric evaluation of the two H0 chart rectangles

The original relative chart pastings evaluate the two complete faces of the same 31-vertex
diagram. The comparison records all levels and both homotopy coordinates, not only endpoints.
Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassH0Native.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Diagram

open SimplexParameters

private theorem ofLevels_continuousMap_eq
    {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H K : Homotopy f g} (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap = (J.level n).toContinuousMap :=
  rfl

private theorem projected_comparison_level
    {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
    (r : C ⟶ A) (r' : C' ⟶ A') (hr : q ≫ p = r) (hr' : q' ≫ p' = r')
    (n : ℕ) :
    ((BoundedFlatPerfectDoubleSquareTrack.originalComparison p q p' q' a b c hp hq).level
        n).toContinuousMap =
      ((DoubleSquareTrack.projectionComparison p q p' q' a b c hp hq r r' hr hr').level
        n).toContinuousMap := by
  unfold DoubleSquareTrack.projectionComparison
  rw [ofLevels_continuousMap_eq]
  unfold BoundedFlatPerfectDoubleSquareTrack.originalComparison DoubleSquareTrack.originalComparison
  simp only [ofLevels_continuousMap_eq]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b)

/-- The complete plus chart rectangle evaluates to the original geometric relative square. -/
theorem plus_rectangle_lift :
    HomotopyLift (simplex P g) (BoundedFlatPerfectProjectionRectangleParameters.rectangle plusFace)
      (boundedAboveFlatCoefficientPlusPasting P g) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex P g) n
    (StdSimplex.map plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, plus_face]
  refine (BoundedFlatPerfectDoubleSquareScalarPaths.original_rectangle_nativeLift
    (polynomialProjection P a) (laurentPlus P a) (polynomialProjection P b) (laurentPlus P b)
    (coefficientMap P g) (coefficientMap P ((polynomialUnderFunctor R).map g))
    (coefficientMap P ((laurentUnderFunctor R).map g)) (polynomialProjection_naturality P g)
    (coefficientMap_naturality_of_natTrans P (underToLaurent R) g) n r s x).trans ?_
  exact DFunLike.congr_fun (projected_comparison_level
    (polynomialProjection P a) (laurentPlus P a) (polynomialProjection P b) (laurentPlus P b)
    (coefficientMap P g) (coefficientMap P ((polynomialUnderFunctor R).map g))
    (coefficientMap P ((laurentUnderFunctor R).map g)) (polynomialProjection_naturality P g)
    (coefficientMap_naturality_of_natTrans P (underToLaurent R) g) (laurentProjection P a)
    (laurentProjection P b) (laurentPlus_projection P a) (laurentPlus_projection P b) n) (r, (s, x))

/-- The complete minus chart rectangle evaluates to the original geometric relative square. -/
theorem minus_rectangle_lift :
    HomotopyLift (simplex P g) (BoundedFlatPerfectProjectionRectangleParameters.rectangle minusFace)
      (boundedAboveFlatCoefficientMinusPasting P g) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex P g) n
    (StdSimplex.map minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, minus_face]
  refine (BoundedFlatPerfectDoubleSquareScalarPaths.original_rectangle_nativeLift
    (polynomialProjection P a) (laurentMinus P a) (polynomialProjection P b) (laurentMinus P b)
    (coefficientMap P g) (coefficientMap P ((polynomialUnderFunctor R).map g))
    (coefficientMap P ((laurentUnderFunctor R).map g)) (polynomialProjection_naturality P g)
    (coefficientMap_naturality_of_natTrans P (underToLaurentInvert R) g) n r s x).trans ?_
  exact DFunLike.congr_fun (projected_comparison_level
    (polynomialProjection P a) (laurentMinus P a) (polynomialProjection P b) (laurentMinus P b)
    (coefficientMap P g) (coefficientMap P ((polynomialUnderFunctor R).map g))
    (coefficientMap P ((laurentUnderFunctor R).map g)) (polynomialProjection_naturality P g)
    (coefficientMap_naturality_of_natTrans P (underToLaurentInvert R) g) (laurentProjection P a)
    (laurentProjection P b) (laurentMinus_projection P a) (laurentMinus_projection P b) n)
    (r, (s, x))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Diagram
