/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputDescSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Native

/-!
# The full original raw input descent surface

The two unchanged geometric rectangle surfaces undergo the original common-outer-path
cancellation and the original ThreeSideSquare quotient. Every native point is retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputDescSimplex
open BoundedFlatPerfectProjectionRectangleParameters
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

private theorem ofLevels_continuousMap_eq
    {E F : Topology.LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H L : Homotopy f g} (J : H.RelHomotopy L) (H' L' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hL : ∀ n, L'.level n = L.level n)
    (n : ℕ) :
    ((J.ofLevels H' L' hH hL).level n).toContinuousMap = (J.level n).toContinuousMap :=
  rfl

private theorem projectedComparison_level {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
    (d : C ⟶ A) (d' : C' ⟶ A') (hd : q ≫ p = d) (hd' : q' ≫ p' = d')
    (n : ℕ) :
    ((BoundedFlatPerfectDoubleSquareTrack.originalComparison p q p' q' a b c hp hq).level
        n).toContinuousMap =
      ((DoubleSquareTrack.projectionComparison p q p' q' a b c hp hq d d' hd hd').level
        n).toContinuousMap := by
  unfold DoubleSquareTrack.projectionComparison
  rw [ofLevels_continuousMap_eq]
  unfold BoundedFlatPerfectDoubleSquareTrack.originalComparison DoubleSquareTrack.originalComparison
  simp only [ofLevels_continuousMap_eq]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The whole positive rectangle retains both original geometric clocks. -/
theorem plus_rectangle_lift :
    HomotopyLift (simplex g) (rectangle BoundedFlatCoefficientBassH0Diagram.plusFace)
      (plusInputPasting g) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex g) n
    (StdSimplex.map BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, plus_face]
  refine (BoundedFlatPerfectDoubleSquareScalarPaths.original_rectangle_nativeLift
    (projection.app Y) (plus.app Y) (projection.app X) (plus.app X) g (polynomial.map g)
    (laurent.map g) (projection.naturality g) (plus.naturality g) n r s x).trans ?_
  exact DFunLike.congr_fun (projectedComparison_level
    (projection.app Y) (plus.app Y) (projection.app X) (plus.app X) g (polynomial.map g)
    (laurent.map g) (projection.naturality g) (plus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (plus_projection Y) (plus_projection X) n) (r, (s, x))

/-- The whole inverse-coordinate rectangle retains both original geometric clocks. -/
theorem minus_rectangle_lift :
    HomotopyLift (simplex g) (rectangle BoundedFlatCoefficientBassH0Diagram.minusFace)
      (minusInputPasting g) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex g) n
    (StdSimplex.map BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, minus_face]
  refine (BoundedFlatPerfectDoubleSquareScalarPaths.original_rectangle_nativeLift
    (projection.app Y) (minus.app Y) (projection.app X) (minus.app X) g (polynomial.map g)
    (laurent.map g) (projection.naturality g) (minus.naturality g) n r s x).trans ?_
  exact DFunLike.congr_fun (projectedComparison_level
    (projection.app Y) (minus.app Y) (projection.app X) (minus.app X) g (polynomial.map g)
    (laurent.map g) (projection.naturality g) (minus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (minus_projection Y) (minus_projection X) n) (r, (s, x))

/-- The complete original outer-track cancellation is evaluated without a replacement filler. -/
theorem boundary_native_lift :
    HomotopyLift (simplex g) BoundedFlatCoefficientBassH0Diagram.boundaryParameter
      (inputBoundary g) := by
  have jp := plus_rectangle_lift g
  have jm := minus_rectangle_lift g
  have sp := HomotopyLift.source (simplex g) jp
  have sm := HomotopyLift.source (simplex g) jm
  have tp := HomotopyLift.target (simplex g) jp
  have tm := HomotopyLift.target (simplex g) jm
  have lLp := PathLift.trans_left (simplex g) sp
  have lPp := PathLift.trans_right (simplex g) sp
  have lLm := PathLift.trans_left (simplex g) sm
  have lPm := PathLift.trans_right (simplex g) sm
  have lDp := PathLift.symm (simplex g) (PathLift.trans_left (simplex g) tp)
  have lDm := PathLift.symm (simplex g) (PathLift.trans_left (simplex g) tm)
  simp only [Path.symm_symm, Homotopy.symm_symm] at lDp lDm
  have lT := PathLift.trans_left (simplex g) (PathLift.trans_right (simplex g) tp)
  have lKp := PathLift.trans_right (simplex g) (PathLift.trans_right (simplex g) tp)
  have lKm := PathLift.trans_right (simplex g) (PathLift.trans_right (simplex g) tm)
  exact HomotopyLift.pasteProjectionSquares (simplex g)
    lDp lDm lT lLp lPp lKp lLm lPm lKm jp jm

/-- Both original endpoint transports preserve every point of the selected descent pasting. -/
theorem desc_native_lift :
    HomotopyLift (simplex g) BoundedFlatCoefficientBassH0Diagram.boundaryParameter
      (inputDescPasting g) := by
  intro n r s x
  exact boundary_native_lift g n r s x

/-- The selected quotient-collapse square retains the entire original input descent surface. -/
theorem square_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    prespectrumSimplexFamily (simplex g) n
        (BoundedFlatCoefficientBassH0Diagram.parameter (r, s), x) =
      (inputDescPasting g).toSquare.level n (r, (s, x)) :=
  HomotopyLift.toSquare (simplex g) (desc_native_lift g) n r s x

/-- The genuine comparison cylinder is the whole original two-chart quotient surface. -/
theorem cylinder_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    prespectrumSimplexFamily (simplex g) n
        (BoundedFlatCoefficientBassH0Diagram.parameter (r, s), x) =
      (inputComparisonHomotopy g).level n
        (r, HomotopyPushout.cylinder
          (K (projection.app Y))
          (K (projection.app Y)) n (s, x)) :=
  (square_native g n r s x).trans (inputComparisonHomotopy_cylinder g n r s x).symm

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputDescSimplex
