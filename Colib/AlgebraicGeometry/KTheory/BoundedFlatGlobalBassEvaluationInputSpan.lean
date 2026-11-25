/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputProjectionSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputConeSource
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputSpan
public import Colib.Topology.Prespectrum.HomotopySquareComposition
public import Colib.Topology.Prespectrum.PushoutIdentityFromUnitSquare
public import Colib.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Original input naturality on the global polynomial span

The moving projection square descends to the literal strict input map followed by evaluation
and the independently defined raw input map after evaluation. The two polynomial charts retain
the original evaluation homotopy without a constant pause. Reassociation of the actual composite
cylinder occurs inside its relative boundary, leaving both moving chart parameters unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
open GlobalSectionChangeIndex
namespace InputSpan
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Strict source transport of the original projection evaluation, with no path change. -/
def sourceLeg : Homotopy
    (sectionMap (projection.app Y) ≫
      (sectionMap (polynomial.map g) ≫ evaluation (polynomial.obj X)))
    ((sectionMap g ≫ evaluation X) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) :=
  (InputProjectionSquare.sourceTrack g).cast
    (by rw [sectionMap_comp]; exact Category.assoc _ _ _) rfl

/-- The pasted leg retains the two original evaluation and raw projection pieces. -/
def pastedLeg :=
  HomotopyPushout.identicalLegPastedTrack
    (sectionMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (evaluation Y) (evaluation (polynomial.obj Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (evaluationComparison (projection.app Y)) (GlobalRawBass.polynomialSquareHomotopy g)

/-- Only endpoint associations change in the original moving projection square. -/
def legSquare : (sourceLeg g).Square (pastedLeg g)
    (Homotopy.precomp (sectionMap (projection.app Y))
      (evaluationComparison (polynomial.map g)))
    ((evaluationComparison g).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))) :=
  (InputProjectionSquare.square g).ofBoundaryLevels _ _ _ _
    (fun _ => rfl)
    (by intro n; apply Homotopy.trans_level_congr <;> rfl)
    (fun _ => rfl) (fun _ => rfl)

/-- The complete source cylinder uses strict precomposition of the original evaluation leg. -/
def sourceCylinder :=
  HomotopyPushout.mapSquareHomotopy
    (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (sectionMap g ≫ evaluation X)
    (sectionMap (polynomial.map g) ≫ evaluation (polynomial.obj X))
    (sectionMap (polynomial.map g) ≫ evaluation (polynomial.obj X))
    (sourceLeg g) (sourceLeg g)

/-- The actual composite cylinder retains the original evaluation and raw span maps. -/
def actualCompositeCylinder :=
  HomotopyPushout.identicalLegActualCompositeTrack
    (sectionMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (evaluation Y) (evaluation (polynomial.obj Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (evaluationComparison (projection.app Y)) (GlobalRawBass.polynomialSquareHomotopy g)

/-- The original polynomial evaluation on the left chart, in its unchanged time coordinate. -/
def leftChart := (evaluationComparison (polynomial.map g)).postcomp
  (HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)))

/-- The same original polynomial evaluation on the right chart, in its unchanged time coordinate. -/
def rightChart := (evaluationComparison (polynomial.map g)).postcomp
  (HomotopyPushout.inr (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)))

/-- Reassociate the target cylinder inside the boundary, preserving the complete chart edges. -/
def cylinderBoundary : (sourceCylinder g).RelHomotopy
    (((Homotopy.precomp (sectionMap (projection.app Y)) (leftChart g)).trans
      (actualCompositeCylinder g)).trans
        (Homotopy.precomp (sectionMap (projection.app Y)) (rightChart g)).symm) := by
  let S := HomotopyPushout.identicalLegMovingSquare
    (sectionMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (sourceLeg g) (pastedLeg g) (evaluationComparison g)
    (evaluationComparison (polynomial.map g)) (legSquare g)
  let R := HomotopyPushout.identicalLegCompositionPasting
    (sectionMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (evaluation Y) (evaluation (polynomial.obj Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (evaluationComparison (projection.app Y)) (GlobalRawBass.polynomialSquareHomotopy g)
  exact S.toBoundary.trans
    (((Homotopy.RelHomotopy.refl
      (Homotopy.precomp (sectionMap (projection.app Y)) (leftChart g))).hcomp R.symm).hcomp
        (Homotopy.RelHomotopy.refl
          (Homotopy.precomp (sectionMap (projection.app Y)) (rightChart g)).symm))

/-- The full moving cylinder has the actual composite target and both unpaused chart edges. -/
def cylinderSquare : (sourceCylinder g).Square (actualCompositeCylinder g)
    (Homotopy.precomp (sectionMap (projection.app Y)) (leftChart g))
    (Homotopy.precomp (sectionMap (projection.app Y)) (rightChart g)) :=
  (cylinderBoundary g).toSquare

/-- The source cylinder is strict precomposition, with no reflexive square-map pieces. -/
theorem sourceCylinder_level (n : ℕ) :
    (sourceCylinder g).level n =
      (Homotopy.precomp (sectionMap g)
        (HomotopyPushout.mapSquareHomotopy
          (sectionMap (projection.app X)) (sectionMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (evaluation X) (evaluation (polynomial.obj X)) (evaluation (polynomial.obj X))
          (evaluationComparison (projection.app X))
          (evaluationComparison (projection.app X)))).level n := by
  unfold sourceCylinder HomotopyPushout.mapSquareHomotopy
  rw [Homotopy.precomp_trans, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The target cylinder is the whole actual composite of the original two span maps. -/
theorem actualCompositeCylinder_level (n : ℕ) :
    (actualCompositeCylinder g).level n =
      ((HomotopyPushout.glue (sectionMap (projection.app Y))
        (sectionMap (projection.app Y))).postcomp
          (spanEvaluation Y ≫ GlobalRawBass.spanMap g)).level n := rfl

/-- Literal quotient descent identifies the source with strict input followed by evaluation. -/
theorem sourceDesc_eq :
    HomotopyPushout.desc (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
      ((sectionMap (polynomial.map g) ≫ evaluation (polynomial.obj X)) ≫
        HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)))
      ((sectionMap (polynomial.map g) ≫ evaluation (polynomial.obj X)) ≫
        HomotopyPushout.inr (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)))
      (sourceCylinder g) = sectionSpanMap g ≫ spanEvaluation X := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (sourceCylinder_level g n) (s, x)

/-- Literal quotient descent identifies the target with the independently defined raw input. -/
theorem targetDesc_eq :
    HomotopyPushout.desc (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
      ((evaluation (polynomial.obj Y) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g)) ≫
        HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)))
      ((evaluation (polynomial.obj Y) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g)) ≫
        HomotopyPushout.inr (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)))
      (actualCompositeCylinder g) = spanEvaluation Y ≫ GlobalRawBass.spanMap g :=
  HomotopyPushout.identicalLegActualCompositeDesc _ _ _ _ _ _ _ _ _

end InputSpan
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Original evaluation compares actual strict and raw input maps on the whole polynomial span. -/
def inputSpanHomotopy :
    Homotopy (InputSpan.sectionSpanMap g ≫ spanEvaluation X)
      (spanEvaluation Y ≫ GlobalRawBass.spanMap g) :=
  (HomotopyPushout.descSquareHomotopy
    (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
    (InputSpan.leftChart g) (InputSpan.rightChart g) (InputSpan.cylinderSquare g)).cast
      (InputSpan.sourceDesc_eq g) (InputSpan.targetDesc_eq g)

/-- The entire left chart is the original polynomial evaluation with no added constant time. -/
theorem inputSpanHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (sectionDiagram.obj (op (polynomial.obj Y))).space n) :
    (inputSpanHomotopy g).level n
      (r, (HomotopyPushout.inl (sectionMap (projection.app Y))
        (sectionMap (projection.app Y))).map n x) =
      (HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))).map n
          ((evaluationComparison (polynomial.map g)).level n (r, x)) := rfl

/-- The entire right chart has exactly the same unchanged polynomial evaluation parameter. -/
theorem inputSpanHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (sectionDiagram.obj (op (polynomial.obj Y))).space n) :
    (inputSpanHomotopy g).level n
      (r, (HomotopyPushout.inr (sectionMap (projection.app Y))
        (sectionMap (projection.app Y))).map n x) =
      (HomotopyPushout.inr (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))).map n
          ((evaluationComparison (polynomial.map g)).level n (r, x)) := rfl

/-- Every original cylinder point retains both independent parameters of the constructed square. -/
theorem inputSpanHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (sectionDiagram.obj (op Y)).space n) :
    (inputSpanHomotopy g).level n
      (r, HomotopyPushout.cylinder (sectionMap (projection.app Y))
        (sectionMap (projection.app Y)) n (s, x)) =
      (InputSpan.cylinderSquare g).level n (r, (s, x)) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
