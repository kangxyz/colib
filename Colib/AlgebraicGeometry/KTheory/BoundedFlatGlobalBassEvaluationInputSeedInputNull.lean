/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputNullCells

/-!
# The whole original mixed input null in both actual carrier sheets

The native equality is proved for the original scalar operation word, including its exact
boundary collapse, composition correction, horizontal pastes, and final quotient descent.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputNull
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual first correction piece is original source-chart evaluation after raw input. -/
abbrev originalFirst := ConeCompositionPieces.first
  (GlobalRawBass.InputIdentityPositive.chart X)
  (GlobalBassEvaluation.evaluation (polynomial.obj Y))
  (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (evaluationComparison (plus.app Y))

/-- The original second piece is the complete raw positive square at evaluated input. -/
abbrev originalSecond := ConeCompositionPieces.second
  (GlobalRawBass.InputIdentityPositive.chart X)
  (GlobalBassEvaluation.evaluation (polynomial.obj Y))
  (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
  (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (GlobalRawBass.plusSquareHomotopy g)

/-- The final piece is the unmodified final cone cylinder. -/
abbrev originalThird := ConeCompositionPieces.third
  (GlobalRawBass.InputIdentityPositive.chart X)
  (GlobalBassEvaluation.evaluation (polynomial.obj Y))
  (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))

/-- The entire source of the original correction keeps the actual nested null clocks. -/
theorem pasted_native (e : Bool) (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (pastedPath g e s) x =
      (((originalFirst g).trans (originalSecond g)).trans (originalThird g)).level n
        (s, input n x) := by
  have h := (congrArg (fun z ↦ nativeEval g n z x)
    ((movingSquare g e).at_one s)).symm.trans
      ((moving_native g e n 1 s x).trans ((originalMoving g).at_one n s (input n x)))
  exact h.trans (DFunLike.congr_fun
    (ConeCompositionPieces.source_level (GlobalRawBass.InputIdentityPositive.chart X)
      (GlobalBassEvaluation.evaluation (polynomial.obj Y))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
      (evaluationComparison (plus.app Y)) (GlobalRawBass.plusSquareHomotopy g) n)
    (s, input n x))

/-- The full correction is the original scalar associator at every native point. -/
theorem correction_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (correction g e (r, s)) x =
      (originalCorrection g).level n (r, (s, input n x)) := by
  let ev := fun z ↦ nativeEval g n z x
  let A := (originalFirst g).path n (input n x)
  let B := (originalSecond g).path n (input n x)
  let C := (originalThird g).path n (input n x)
  have hP (t : I) : ev (pastedPath g e t) = ((A.trans B).trans C) t := by
    dsimp only [ev, A, B, C]
    rw [← Homotopy.path_trans, ← Homotopy.path_trans]
    exact pasted_native g e n t x
  have hAB := Path.Evaluation.left_factor ev
    ((edge g e 3 4).trans (rawPath g e)) (targetCylinder g e) (A.trans B) C hP
  have hC := Path.Evaluation.right_factor ev
    ((edge g e 3 4).trans (rawPath g e)) (targetCylinder g e) (A.trans B) C hP
  have hA := Path.Evaluation.left_factor ev (edge g e 3 4) (rawPath g e) A B hAB
  have hB := Path.Evaluation.right_factor ev (edge g e 3 4) (rawPath g e) A B hAB
  rw [ConeCompositionPieces.correction_apply]
  exact Path.Evaluation.transAssoc ev (edge g e 3 4) (rawPath g e) (targetCylinder g e)
    A B C hA hB hC r s

/-- The fixed original inclusion track is retained along the whole left edge. -/
abbrev originalLeft := Homotopy.precomp (InputPositive.strictChart Y)
  ((evaluationComparison (laurent.map g)).postcomp
    (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)))

/-- The original terminal track remains its native constant track. -/
abbrev originalRight := Topology.LoopPrespectrum.Homotopy.refl
  (zeroHom (sectionDiagram.obj (op (polynomial.obj Y)))
    (mappingCone (GlobalRawBass.InputIdentityPositive.chart X)))

/-- The actual full native boundary word used by the frozen moving-null producer. -/
abbrev originalBoundary :=
  (originalMoving g).toBoundary.trans
    ((((Homotopy.RelHomotopy.refl (originalLeft g)).hcomp (originalCorrection g))).hcomp
      (Homotopy.RelHomotopy.refl (originalRight (X := X) (Y := Y))).symm)

/-- The entire Laurent edge, without adding a constant initial or terminal segment. -/
theorem left_native (e : Bool) (n : ℕ) (r : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (edge g e 0 3 r) x = (originalLeft g).level n (r, input n x) :=
  (congrArg (fun z ↦ nativeEval g n z x) ((movingSquare g e).left r)).symm.trans
    ((moving_native g e n r 0 x).trans ((originalMoving g).left n r (input n x)))

/-- Every point of the exact collapsed-boundary and horizontal-correction word is native. -/
theorem boundary_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (boundaryComparison g e (r, s)) x =
      (originalBoundary g).level n (r, (s, input n x)) := by
  let ev := fun z ↦ nativeEval g n z x
  let L := Path.Homotopy.refl (edge g e 0 3)
  let L' := Homotopy.RelHomotopy.refl (originalLeft g)
  let R := (Path.Homotopy.refl (Path.refl (tip g e))).symm
  let R' := (Homotopy.RelHomotopy.refl (originalRight (X := X) (Y := Y))).symm
  let C := L.hcomp (correction g e)
  let C' := L'.hcomp (originalCorrection g)
  have hC (a b : I) : ev (C (a, b)) = C'.level n (a, (b, input n x)) :=
    (Path.Evaluation.comparison_hcomp ev L (correction g e)
      (L'.path n (input n x)) ((originalCorrection g).path n (input n x))
      (fun _ t ↦ left_native g e n t x) (fun t w ↦ correction_native g e n t w x) a b).trans
      (Homotopy.RelHomotopy.hcomp_apply_path L' (originalCorrection g) n a b (input n x)).symm
  have hR (a b : I) : ev (R (a, b)) = R'.level n (a, (b, input n x)) :=
    tip_native g e n x
  have hD (a b : I) : ev ((C.hcomp R) (a, b)) =
      (C'.hcomp R').level n (a, (b, input n x)) :=
    (Path.Evaluation.comparison_hcomp ev C R (C'.path n (input n x))
      (R'.path n (input n x)) hC hR a b).trans
      (Homotopy.RelHomotopy.hcomp_apply_path C' R' n a b (input n x)).symm
  exact (Path.Evaluation.comparison_trans ev (movingSquare g e).toBoundary (C.hcomp R)
    ((originalMoving g).toBoundary.path n (input n x)) ((C'.hcomp R').path n (input n x))
    (fun a b ↦ moving_native g e n (Topology.ThreeSideSquare.collapse (a, b)).1
      (Topology.ThreeSideSquare.collapse (a, b)).2 x) hD r s).trans
    (Homotopy.RelHomotopy.trans_apply_path (originalMoving g).toBoundary (C'.hcomp R')
      n r s (input n x)).symm

/-- Both original sheet surfaces equal the unchanged whole positive null at strict projection. -/
theorem native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (parameter g e (r, s)) x =
      (InputPositive.nullSquare g).level n (r, (s, input n x)) := by
  exact Topology.CarrierPathSquare.boundarySquare_native
    (m := Path.refl (tip g e)) (M := originalRight (X := X) (Y := Y))
    (boundaryComparison g e) (originalBoundary g) n (input n x)
    (fun z ↦ nativeEval g n z x) (fun a b ↦ boundary_native g e n a b x) r s

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputNull
