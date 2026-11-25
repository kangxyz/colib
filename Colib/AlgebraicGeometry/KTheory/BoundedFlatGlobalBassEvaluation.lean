/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationBoundary
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting
public import Colib.Topology.Prespectrum.PushoutHomotopySquare
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Topology.Prespectrum.ConeHomotopySquare
public import Colib.KTheory.Bass.StrictDiagram

/-!
# The actual one-step global Bass evaluation

The proved original geometric overlap descends to the actual raw polynomial double cylinder,
Laurent comparison, cone and parameter loops. The evaluation naturality tracks remain literal
on both charts and the full cylinder. Original source-null and seed compatibility are separate
obligations; this module does not construct an arbitrary-stage raw tower.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
open GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- Original evaluation maps the whole strict section span to the actual raw geometric span. -/
def spanEvaluation : StrictSquare.span (sectionSquare X) ⟶ GlobalRawBass.span X :=
  HomotopyPushout.mapOfHomotopies
    (sectionMap (projection.app X)) (sectionMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (evaluation X) (evaluation (polynomial.obj X)) (evaluation (polynomial.obj X))
    (evaluationComparison (projection.app X)) (evaluationComparison (projection.app X))

/-- Source cylinder endpoints regroup for literal quotient descent. -/
def sourceDescTrack := (sourceTrack X).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Target cylinder endpoints regroup for the same actual quotient descent. -/
def targetDescTrack := (targetTrack X).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Both whole original Laurent boundaries are precomposed by the actual strict source legs. -/
def pastedDescTrack :=
  ((Homotopy.precomp (sectionMap (projection.app X)) (evaluationComparison (plus.app X))).trans
    (targetDescTrack X)).trans
      (Homotopy.precomp (sectionMap (projection.app X)) (evaluationComparison (minus.app X))).symm

/-- The genuine original overlap supplies the complete moving-descent interface. -/
def descPasting : (sourceDescTrack X).RelHomotopy (pastedDescTrack X) :=
  (pasting X).ofLevels _ _ (fun _ => rfl) (by
    intro n
    apply Homotopy.trans_level_congr
    · apply Homotopy.trans_level_congr <;> rfl
    · rfl)

/-- The target cylinder is the actual span-map cylinder followed by the original raw comparison. -/
theorem targetDescTrack_level (n : ℕ) :
    (targetDescTrack X).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (sectionMap (projection.app X)) (sectionMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (evaluation X) (evaluation (polynomial.obj X)) (evaluation (polynomial.obj X))
        (evaluationComparison (projection.app X))
        (evaluationComparison (projection.app X))).postcomp
          (GlobalRawBass.comparison X)).level n := by
  simp only [targetDescTrack, Homotopy.cast_level, targetTrack,
    HomotopyPushout.mapSquareHomotopy, Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · rfl
    · exact congrArg (fun H => H.level n)
        (Homotopy.postcomp_symm (evaluationComparison (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X))).symm

/-- Source descent is the original strict comparison followed by unchanged Laurent evaluation. -/
theorem sourceDesc_eq :
    HomotopyPushout.desc (sectionMap (projection.app X)) (sectionMap (projection.app X))
      (sectionMap (plus.app X) ≫ evaluation (laurent.obj X))
      (sectionMap (minus.app X) ≫ evaluation (laurent.obj X)) (sourceDescTrack X) =
      StrictSquare.comparison (sectionSquare X) ≫ evaluation (laurent.obj X) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- Target descent is the actual span evaluation followed by the unchanged raw comparison. -/
theorem targetDesc_eq :
    HomotopyPushout.desc (sectionMap (projection.app X)) (sectionMap (projection.app X))
      (evaluation (polynomial.obj X) ≫ boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))
      (evaluation (polynomial.obj X) ≫ boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X))
      (targetDescTrack X) = spanEvaluation X ≫ GlobalRawBass.comparison X := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (targetDescTrack_level X n) (s, x)

/-- The complete original overlap descends to the two unchanged comparison-map composites. -/
def comparisonHomotopy :
    Homotopy (StrictSquare.comparison (sectionSquare X) ≫ evaluation (laurent.obj X))
      (spanEvaluation X ≫ GlobalRawBass.comparison X) :=
  (HomotopyPushout.descSquareHomotopy (H₀ := sourceDescTrack X) (H₁ := targetDescTrack X)
    (sectionMap (projection.app X)) (sectionMap (projection.app X))
    (evaluationComparison (plus.app X)) (evaluationComparison (minus.app X))
    (descPasting X).toSquare).cast (sourceDesc_eq X) (targetDesc_eq X)

/-- The complete original positive-chart evaluation track remains the first face. -/
theorem comparisonHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (sectionDiagram.obj (op (polynomial.obj X))).space n) :
    (comparisonHomotopy X).level n
      (r, (HomotopyPushout.inl (sectionMap (projection.app X))
        (sectionMap (projection.app X))).map n x) =
      (evaluationComparison (plus.app X)).level n (r, x) := rfl

/-- The distinct inverse-coordinate evaluation track remains the other face. -/
theorem comparisonHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (sectionDiagram.obj (op (polynomial.obj X))).space n) :
    (comparisonHomotopy X).level n
      (r, (HomotopyPushout.inr (sectionMap (projection.app X))
        (sectionMap (projection.app X))).map n x) =
      (evaluationComparison (minus.app X)).level n (r, x) := rfl

/-- The full original double cylinder is the proved moving evaluation square. -/
theorem comparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (sectionDiagram.obj (op X)).space n) :
    (comparisonHomotopy X).level n
      (r, HomotopyPushout.cylinder (sectionMap (projection.app X))
        (sectionMap (projection.app X)) n (s, x)) =
      (descPasting X).toSquare.level n (r, (s, x)) := rfl

/-- Original evaluation and the actual overlap map the literal Bass cones. -/
def coneEvaluation : mappingCone (StrictSquare.comparison (sectionSquare X)) ⟶
    mappingCone (GlobalRawBass.comparison X) :=
  mappingConeSquareMap (StrictSquare.comparison (sectionSquare X)) (GlobalRawBass.comparison X)
    (spanEvaluation X) (evaluation (laurent.obj X)) (comparisonHomotopy X)

/-- Laurent evaluation remains literal on the original cone inclusion. -/
theorem coneEvaluation_inclusion :
    mappingConeInclusion (StrictSquare.comparison (sectionSquare X)) ≫ coneEvaluation X =
      evaluation (laurent.obj X) ≫ mappingConeInclusion (GlobalRawBass.comparison X) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- The source is literally the existing global strict Bass functor's one-step value. -/
theorem sectionStep_eq :
    ((KTheory.Bass.strictDiagramFunctor squareFunctor).obj
      sectionDiagram).obj (op X) =
      parameterLooping (mappingCone (StrictSquare.comparison (sectionSquare X))) := rfl

/-- Parameter looping gives the actual one-step strict-section to raw Bass evaluation. -/
def stepEvaluation :
    parameterLooping (mappingCone (StrictSquare.comparison (sectionSquare X))) ⟶
      GlobalRawBass.step X :=
  parameterLoopingMap (coneEvaluation X)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
