/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterCells
public import Colib.Topology.Path.SpanReassociationPointwise
public import Colib.Topology.Prespectrum.SpanReassociationEvaluation

/-!
# The actual native five-piece span reassociation

The whole top of the native moving square determines all five original leaves. Pointwise
naturality preserves the complete three-stage reassociation before raw postcomposition.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterAssoc
open GlobalSectionChangeIndex InputSpanParameterWord InputSpanParameterCells
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual original five-piece relative comparison selected by the input span. -/
def reassociationNative := HomotopyPushout.identicalLegCompositionPasting
  (sectionMap (projection.app Y))
  (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
  (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
  (evaluation Y) (evaluation (polynomial.obj Y))
  (boundedAboveFlatPerfectPullbackPrespectrumMap g)
  (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
  (evaluationComparison (projection.app Y)) (GlobalRawBass.polynomialSquareHomotopy g)

/-- Whole top-word evaluation recovers all original reassociation stages and clocks. -/
theorem reassociation_native (n : ℕ)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n)
      (r s : unitInterval) :
    ev g n x (reassociation g (r, s)) =
      (GlobalRawBass.comparison X).map n ((reassociationNative g).level n (r, (s, x))) := by
  let a := evaluation Y
  let c := boundedAboveFlatPerfectPullbackPrespectrumMap g
  let d := boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g)
  let h := boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)
  let j := boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y)
  let H := evaluationComparison (projection.app Y)
  let K := GlobalRawBass.polynomialSquareHomotopy g
  let iL := HomotopyPushout.inl h h
  let iR := HomotopyPushout.inr h h
  let P := H.postcomp (d ≫ iL)
  let Q : Homotopy ((a ≫ j) ≫ (d ≫ iL)) ((a ≫ c) ≫ (h ≫ iL)) :=
    (Homotopy.precomp a (K.postcomp iL)).cast
      (by simp only [d, h, j, Category.assoc]) (by simp only [c, h, Category.assoc])
  let T := Homotopy.precomp (a ≫ c) (HomotopyPushout.glue h h)
  let U : Homotopy ((a ≫ c) ≫ (h ≫ iR)) ((a ≫ j) ≫ (d ≫ iR)) :=
    (Homotopy.precomp a (K.symm.postcomp iR)).cast
      (by simp only [c, h, Category.assoc]) (by simp only [d, h, j, Category.assoc])
  let V := H.symm.postcomp (d ≫ iR)
  have hn (t v : unitInterval) :
      Path.Homotopy.spanReassociation (P.path n x) (Q.path n x) (T.path n x)
        (U.path n x) (V.path n x) (t, v) =
      (reassociationNative g).level n (t, (v, x)) := by
    exact Topology.LoopPrespectrum.NativeSpanReassociation.word n x id
      (P.path n x) (Q.path n x) (T.path n x) (U.path n x) (V.path n x)
      P Q T U V (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) t v
  have ht (v : unitInterval) :
      ev g n x (pastedTop g v) = (GlobalRawBass.comparison X).map n
        ((((P.path n x).trans (Q.path n x)).trans
          ((T.path n x).trans ((U.path n x).trans (V.path n x)))) v) := by
    have htop := hn 1 v
    rw [ContinuousMap.HomotopyWith.apply_one] at htop
    calc
      _ = (GlobalRawBass.comparison X).map n ((movingNative g).level n (1, (v, x))) := by
        rw [pastedTop_apply]
        exact moving_native g n x 1 v
      _ = (GlobalRawBass.comparison X).map n
          ((reassociationNative g).level n (1, (v, x))) := by
        apply congrArg
        exact ((movingNative g).at_one n v x).trans
          (((reassociationNative g).level n).apply_one (v, x)).symm
      _ = _ := congrArg ((GlobalRawBass.comparison X).map n) htop.symm
  exact (Path.Evaluation.spanReassociation_of_target_function (ev g n x)
    ((GlobalRawBass.comparison X).map n)
    (firstPlus g) (lastPlus g) (overlapTop g) (lastMinus g).symm (firstMinus g).symm
    (P.path n x) (Q.path n x) (T.path n x) (U.path n x) (V.path n x) ht r s).trans
      (congrArg ((GlobalRawBass.comparison X).map n) (hn r s))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterAssoc
