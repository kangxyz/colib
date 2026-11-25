/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationComposition
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassStep
public import Colib.Topology.Prespectrum.RelativeHomotopySquarePasting

/-!
# The original global Laurent-chart evaluation pasting

Each actual positive or inverse chart specializes the proved original evaluation composition
relation. The source transport uses only the geometric chart equation, and all original
comparison and geometric track values remain unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
open GlobalSectionChangeIndex

/-- The actual global section prespectrum diagram on all schemes. -/
abbrev sectionDiagram := boundedAboveFlatGlobalSectionModelFunctor.{u} ⋙ prespectrumFunctor

/-- The actual strict section square on the original geometric polynomial and Laurent products. -/
def sectionSquare (X : Scheme.{u}) :=
  sectionDiagram.mapArrow.mapArrow.obj (square (op X))

/-- Original normalized evaluation on the actual scheme fiber. -/
def evaluation (X : Scheme.{u}) := prespectrumMap (evaluationModel (op X))

/-- Original strict reindexing on every actual scheme map. -/
def sectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  sectionDiagram.map f.op

/-- Strict reindex composition retains the original geometric composite. -/
theorem sectionMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sectionMap (f ≫ g) = sectionMap g ≫ sectionMap f :=
  sectionDiagram.map_comp g.op f.op

variable (X : Scheme.{u}) (k : laurent.obj X ⟶ polynomial.obj X)
  (h : k ≫ projection.app X = GlobalRawBass.laurentProjection.app X)

/-- The original chart geometric track, including both original normalization segments. -/
def chartGeometricTrack :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (GlobalRawBass.laurentProjection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap k) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy k (projection.app X)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap h) rfl

/-- Original evaluation followed by the actual chart geometric composition. -/
def chartOuterTrack :
    Homotopy
      (sectionMap (GlobalRawBass.laurentProjection.app X) ≫ evaluation (laurent.obj X))
      ((evaluation X ≫ boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap k) :=
  (evaluationComparison (GlobalRawBass.laurentProjection.app X)).trans
    ((Homotopy.precomp (evaluation X) (chartGeometricTrack X k h)).cast
      rfl (Category.assoc _ _ _).symm)

/-- The unchanged second evaluation track is precomposed by original strict polynomial pullback. -/
def chartFirstTrack :
    Homotopy
      (sectionMap (GlobalRawBass.laurentProjection.app X) ≫ evaluation (laurent.obj X))
      ((sectionMap (projection.app X) ≫ evaluation (polynomial.obj X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap k) :=
  (Homotopy.precomp (sectionMap (projection.app X)) (evaluationComparison k)).cast
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ evaluation (laurent.obj X))
        ((sectionMap_comp k (projection.app X)).symm.trans (congrArg sectionMap h))))
    (Category.assoc _ _ _).symm

/-- The actual first evaluation track is postcomposed by the unchanged raw chart map. -/
def chartSecondTrack :
    Homotopy
      ((sectionMap (projection.app X) ≫ evaluation (polynomial.obj X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap k)
      ((evaluation X ≫ boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap k) :=
  (evaluationComparison (projection.app X)).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap k)

/-- The original two chart-evaluation routes are relatively homotopic with fixed endpoints. -/
def chartPasting :
    ((chartFirstTrack X k h).trans (chartSecondTrack X k)).RelHomotopy
      (chartOuterTrack X k h) := by
  apply (evaluationCompositionRelHomotopy k (projection.app X)).symm.ofLevels _ _
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr
    · have level_congr {A B : Scheme.{u}} {f g : A ⟶ B} (e : f = g) :
          (evaluationComparison f).level n = (evaluationComparison g).level n := by
        subst e
        rfl
      exact (level_congr h).symm
    · rfl

/-- The same chart track on the uncollapsed original strict source leg. -/
def chartMovingTrack :=
  (Homotopy.precomp (sectionMap (projection.app X)) (evaluationComparison k)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- Source endpoint transport does not change any value of the original moving chart track. -/
theorem chartMovingTrack_level (n : ℕ) :
    (chartMovingTrack X k).level n = (chartFirstTrack X k h).level n := rfl

/-- The positive chart specializes to the original raw positive geometric track. -/
theorem chartGeometricTrack_plus :
    chartGeometricTrack X (plus.app X) (GlobalRawBass.plus_projection X) =
      GlobalRawBass.plusHomotopy X := rfl

/-- The inverse chart specializes separately to the original raw inverse geometric track. -/
theorem chartGeometricTrack_minus :
    chartGeometricTrack X (minus.app X) (GlobalRawBass.minus_projection X) =
      GlobalRawBass.minusHomotopy X := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
