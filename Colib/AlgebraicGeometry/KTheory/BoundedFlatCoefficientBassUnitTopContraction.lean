/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopMoving

/-! The original target contraction of the raw Bass identity top, with the
literal scalar and native clocks. Adapted from Quillen
`CoefficientPolynomialSpanUnitTop.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

private theorem family_parameter_congr
    {V U : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {k : ℕ} (S : ModelSimplex V U k) (n : ℕ)
    (z w : StdSimplex ℝ (Fin (k + 1))) (h : z = w) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily S n (w, x) :=
  congrArg (fun v ↦ prespectrumSimplexFamily S n (v, x)) h

/-- Retain the original two constant-cylinder contractions, without changing their speeds. -/
def targetContraction :
    ((Path.refl (StdSimplex.single 22)).trans
      (middleEnd.trans (Path.refl (StdSimplex.single 24)))).Homotopy middleEnd :=
  (Path.Homotopy.reflTrans (middleEnd.trans (Path.refl (StdSimplex.single 24)))).trans
    (Path.Homotopy.transRefl middleEnd)

/-- The original identity-span parameter: boundary extraction, both contractions, then descent. -/
def topBoundary := movingSquare.{u}.toBoundary.trans
  (((Path.Homotopy.refl (binaryPath (k := 24) 2 3 22)).hcomp targetContraction).hcomp
    (Path.Homotopy.refl (binaryPath (k := 24) 7 8 24).symm))

/-- The three-side collapse of the original contracted top boundary. -/
def topParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  collapsed topBoundary.{u}

/-- The complete lower edge keeps the original positive, overlap, inverse word and association. -/
theorem top_zero (t : unitInterval) :
    topParameter.{u} (0, t) =
      (((binaryPath (k := 24) 0 1 2).symm.trans (binaryPath 0 4 12)).trans
        (middleStart.trans
          ((binaryPath 5 6 7).symm.trans (binaryPath 5 9 14)).symm)) t :=
  (ParameterSquare.ofBoundary topBoundary.{u}).at_zero t

/-- Both target pauses have been contracted at the exact original speed. -/
theorem top_one (t : unitInterval) : topParameter.{u} (1, t) = middleEnd t :=
  (ParameterSquare.ofBoundary topBoundary.{u}).at_one t

/-- The whole positive endpoint is the original two-step polynomial identity track. -/
theorem top_left (r : unitInterval) :
    topParameter.{u} (r, 0) = binaryPath (k := 24) 2 3 22 r :=
  (ParameterSquare.ofBoundary topBoundary.{u}).left r

/-- The inverse endpoint keeps its separate original two-step polynomial identity track. -/
theorem top_right (r : unitInterval) :
    topParameter.{u} (r, 1) = binaryPath (k := 24) 7 8 24 r :=
  (ParameterSquare.ofBoundary topBoundary.{u}).right r

/-- The unpaused original cylinder is the terminal row of the actual product grid. -/
theorem cylinder_native : PathLift (simplex P a) middleEnd
    ((HomotopyPushout.glue (polynomialMap P a) (polynomialMap P a)).postcomp
      (comparisonMap P a)) := by
  intro n s x
  refine (family_parameter_congr (simplex P a) n _ _ (middleSquare.at_one s).symm x).trans ?_
  refine (middle_native P a n 1 s x).trans ?_
  exact congrArg (fun y ↦ (comparisonMap P a).map n
    (HomotopyPushout.cylinder (polynomialMap P a) (polynomialMap P a) n (s, y)))
    ((boundedAboveFlatCoefficientIdentityHomotopy P a).at_one n x)

/-- The scalar terminal vertex is the exact target of the unchanged original cylinder. -/
theorem cylinder_target_native : PathLift (simplex P a) (Path.refl (StdSimplex.single 24))
    ((Topology.LoopPrespectrum.Homotopy.refl ((polynomialMap P a) ≫
      HomotopyPushout.inr (polynomialMap P a) (polynomialMap P a))).postcomp
      (comparisonMap P a)) := by
  intro n t x
  refine (family_parameter_congr (simplex P a) n _ _ middleEnd.target.symm x).trans ?_
  exact (cylinder_native P a n 1 x).trans (congrArg ((comparisonMap P a).map n)
    ((HomotopyPushout.glue (polynomialMap P a) (polynomialMap P a)).at_one n x))

/-- Both original constant pieces of the target cylinder contract with their exact native speeds. -/
theorem target_contraction_native : HomotopyLift (simplex P a) targetContraction
    ((HomotopyPushout.identicalLegIdentityTargetComparison (polynomialMap P a)).postcomp
      (comparisonMap P a)) := by
  have h := cylinder_native P a
  have hc := cylinder_target_native P a
  have hp := PathLift.postcompTrans (simplex P a) (comparisonMap P a) h hc
  exact HomotopyLift.postcompTrans (simplex P a) (comparisonMap P a)
    (PathLift.postcompReflTrans (simplex P a) (comparisonMap P a) hp)
    (PathLift.postcompTransRefl (simplex P a) (comparisonMap P a) h)

/-- The whole left endpoint track of the moving square is the original polynomial unit. -/
theorem left_native : PathLift (simplex P a) (binaryPath (k := 24) 2 3 22)
    ((Homotopy.precomp (polynomialMap P a)
      ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        (HomotopyPushout.inl (polynomialMap P a) (polynomialMap P a)))).postcomp
      (comparisonMap P a)) := by
  intro n r x
  refine (family_parameter_congr (simplex P a) n _ _ (plusSquare.left r).symm x).trans ?_
  refine (plus_native P a n r 0 x).trans ?_
  exact congrArg ((K (laurentPlus P a)).map n)
    ((boundedAboveFlatCoefficientPolynomialIdentitySquare P a).left n r x)

/-- The whole right endpoint track retains the separate inverse Laurent chart. -/
theorem right_native : PathLift (simplex P a) (binaryPath (k := 24) 7 8 24)
    ((Homotopy.precomp (polynomialMap P a)
      ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        (HomotopyPushout.inr (polynomialMap P a) (polynomialMap P a)))).postcomp
      (comparisonMap P a)) := by
  intro n r x
  refine (family_parameter_congr (simplex P a) n _ _
    ((unitFaceSquare minusFace).left r).symm x).trans ?_
  refine (minus_native P a n r 0 x).trans ?_
  exact congrArg ((K (laurentMinus P a)).map n)
    ((boundedAboveFlatCoefficientPolynomialIdentitySquare P a).left n r x)

/-- Every point of the original polynomial-span identity cylinder after the unchanged Bass map
has this explicit common-simplex parameter. No span identity or comparison track is replaced. -/
theorem top_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (topParameter.{u} (r, t), x) =
      ((boundedAboveFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
        (boundedAboveFlatCoefficientBassSquareComparison P a)).level n
        (r, HomotopyPushout.cylinder (polynomialMap P a) (polynomialMap P a) n (t, x)) := by
  have hm : HomotopyLift (simplex P a) movingSquare.{u}.toBoundary
      ((movingNative P a).toBoundary.postcomp (comparisonMap P a)) :=
    SquareLift.toBoundary (simplex P a) (moving_native P a)
  let L := Homotopy.precomp (polynomialMap P a)
    ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
      (HomotopyPushout.inl (polynomialMap P a) (polynomialMap P a)))
  let M := Homotopy.precomp (polynomialMap P a)
    ((boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
      (HomotopyPushout.inr (polynomialMap P a) (polynomialMap P a)))
  have hl : HomotopyLift (simplex P a)
      (Path.Homotopy.refl (binaryPath (k := 24) 2 3 22))
      ((Homotopy.RelHomotopy.refl L).postcomp (comparisonMap P a)) := by
    intro n r s x
    exact left_native P a n s x
  have hr : HomotopyLift (simplex P a)
      (Path.Homotopy.refl (binaryPath (k := 24) 7 8 24).symm)
      ((Homotopy.RelHomotopy.refl M.symm).postcomp (comparisonMap P a)) := by
    intro n r s x
    exact right_native P a n (unitInterval.symm s) x
  have hc := HomotopyLift.postcompHcomp (simplex P a) (comparisonMap P a)
    (HomotopyLift.postcompHcomp (simplex P a) (comparisonMap P a)
      hl (target_contraction_native P a)) hr
  have h := HomotopyLift.postcompTrans (simplex P a) (comparisonMap P a) hm hc
  exact (HomotopyLift.postcompOfBoundary (simplex P a) (comparisonMap P a) h n r t x).trans
    (congrArg ((comparisonMap P a).map n)
      (HomotopyPushout.identicalLegIdentityHomotopy_cylinder (polynomialMap P a)
        (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (𝟙 a))
        (boundedAboveFlatCoefficientIdentityHomotopy P a)
        (boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a)
        (boundedAboveFlatCoefficientPolynomialIdentitySquare P a) n r t x)).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop
