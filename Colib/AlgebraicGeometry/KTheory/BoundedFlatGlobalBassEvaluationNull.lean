/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationSourceLeg
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Colib.Topology.Prespectrum.RelativeHomotopyPasting

/-!
# Original Bass nullhomotopies under section evaluation

The proved positive-chart pasting and actual source-leg cone square compare the unchanged
strict and raw Laurent nullhomotopies, preserving every original cylinder parameter.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluationNull
open GlobalBassEvaluation GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- Original positive chart evaluation, with only its strict starting equality transported. -/
def positiveMovement :=
  (chartFirstTrack X (plus.app X) (GlobalRawBass.plus_projection X)).postcomp
    (mappingConeInclusion (GlobalRawBass.comparison X))

/-- The original polynomial evaluation track followed by the raw positive Laurent leg. -/
def polynomialMovement :=
  (chartSecondTrack X (plus.app X)).postcomp
    (mappingConeInclusion (GlobalRawBass.comparison X))

/-- The unchanged Laurent coefficient evaluation track followed by raw cone inclusion. -/
def laurentMovement :=
  (evaluationComparison (GlobalRawBass.laurentProjection.app X)).postcomp
    (mappingConeInclusion (GlobalRawBass.comparison X))

/-- Original raw positive composition, preceded by the original base evaluation. -/
def newPositive : Topology.LoopPrespectrum.Homotopy
    ((GlobalBassEvaluation.evaluation X ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (GlobalRawBass.laurentProjection.app X)) ≫
        mappingConeInclusion (GlobalRawBass.comparison X))
    (((GlobalBassEvaluation.evaluation X ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
          mappingConeInclusion (GlobalRawBass.comparison X)) :=
  ((Homotopy.precomp (GlobalBassEvaluation.evaluation X)
    (GlobalRawBass.plusHomotopy X)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (GlobalRawBass.comparison X))

/-- The actual positive-chart geometric equation retains its whole cone image. -/
def positivePasting :
    ((positiveMovement X).trans (polynomialMovement X)).RelHomotopy
      ((laurentMovement X).trans (newPositive X)) := by
  refine ((chartPasting X (plus.app X) (GlobalRawBass.plus_projection X)).postcomp
      (mappingConeInclusion (GlobalRawBass.comparison X))).ofLevels _ _ ?_ ?_
  · intro n
    exact congrArg (fun H => H.level n)
      (Homotopy.postcomp_trans
        (chartFirstTrack X (plus.app X) (GlobalRawBass.plus_projection X))
        (chartSecondTrack X (plus.app X)) (mappingConeInclusion (GlobalRawBass.comparison X))).symm
  · intro n
    simp only [chartOuterTrack, chartGeometricTrack_plus, Homotopy.postcomp_trans,
      laurentMovement, newPositive]

/-- The evaluated strict source leg traverses the original raw cone cylinder. -/
def oldCone : Topology.LoopPrespectrum.Homotopy
    (((sectionMap (projection.app X) ≫
      GlobalBassEvaluation.evaluation (polynomial.obj X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
          mappingConeInclusion (GlobalRawBass.comparison X))
            (Topology.LoopPrespectrum.zeroHom _ _) :=
  (Homotopy.precomp (StrictSquare.sourceLeg (sectionSquare X) ≫
    spanEvaluation X)
    (mappingConeHomotopy (GlobalRawBass.comparison X))).cast
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        rfl) rfl

/-- The base evaluation followed by the raw source leg traverses that same cone cylinder. -/
def newCone : Topology.LoopPrespectrum.Homotopy
    (((GlobalBassEvaluation.evaluation X ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
          mappingConeInclusion (GlobalRawBass.comparison X))
            (Topology.LoopPrespectrum.zeroHom _ _) :=
  (Homotopy.precomp (GlobalBassEvaluation.evaluation X ≫
    GlobalRawBass.sourceLeg X) (mappingConeHomotopy (GlobalRawBass.comparison X))).cast
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        rfl) rfl

/-- The actual source-leg cone square supplies the whole polynomial-movement boundary. -/
def conePasting :
    (oldCone X).RelHomotopy ((polynomialMovement X).trans (newCone X)) := by
  let Z := Topology.LoopPrespectrum.Homotopy.refl
    (Topology.LoopPrespectrum.zeroHom (sectionDiagram.obj (Opposite.op X))
      (mappingCone (GlobalRawBass.comparison X)))
  have J : (oldCone X).RelHomotopy
      (((polynomialMovement X).trans (newCone X)).trans Z) := by
    refine (sourceLegConeBoundary X).ofLevels _ _ ?_ ?_
    · intro n; rfl
    · intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr
        · apply ContinuousMap.ext; rintro ⟨s, x⟩; rfl
        · rfl
      · rfl
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

/-- Original geometric pasting combines with the cone movement without changing any track. -/
def pastedNullComparison :
    ((positiveMovement X).trans (oldCone X)).RelHomotopy
      ((laurentMovement X).trans ((newPositive X).trans (newCone X))) :=
  ((Homotopy.RelHomotopy.refl (positiveMovement X)).hcomp (conePasting X)).trans
    ((Homotopy.RelHomotopy.transAssoc _ _ _).symm.trans
      (((positivePasting X).hcomp (Homotopy.RelHomotopy.refl (newCone X))).trans
        (Homotopy.RelHomotopy.transAssoc _ _ _)))

/-- The unchanged strict nullhomotopy followed by the actual proved cone evaluation. -/
def originalOldNull : Topology.LoopPrespectrum.Homotopy
    ((sectionMap (GlobalRawBass.laurentProjection.app X) ≫
      GlobalBassEvaluation.evaluation (laurent.obj X)) ≫
        mappingConeInclusion (GlobalRawBass.comparison X))
            (Topology.LoopPrespectrum.zeroHom _ _) :=
  ((strictSourceNull X).postcomp
    (coneEvaluation X)).cast
      (by rw [Category.assoc, coneEvaluation_inclusion,
        ← Category.assoc])
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        exact (coneEvaluation X).map_point n)

/-- The unchanged raw nullhomotopy preceded by the actual original base evaluation. -/
def originalNewNull : Topology.LoopPrespectrum.Homotopy
    ((GlobalBassEvaluation.evaluation X ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (GlobalRawBass.laurentProjection.app X)) ≫
        mappingConeInclusion (GlobalRawBass.comparison X))
            (Topology.LoopPrespectrum.zeroHom _ _) :=
  (Homotopy.precomp (GlobalBassEvaluation.evaluation X)
    (GlobalRawBass.sourceNull X)).cast (Category.assoc _ _ _).symm rfl

/-- Every original raw-null coordinate retains its positive track and actual cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull X).level n = ((newPositive X).trans (newCone X)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level, GlobalRawBass.sourceNull, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · rfl

/-- The original strict-null image retains the full comparison track and raw cone coordinate. -/
theorem originalOldNull_level (n : ℕ) :
    (originalOldNull X).level n = ((positiveMovement X).trans (oldCone X)).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  rfl

/-- The unchanged original Laurent nullhomotopies compare along actual Laurent evaluation. -/
def originalNullComparison :
    (originalOldNull X).RelHomotopy ((laurentMovement X).trans (originalNewNull X)) := by
  refine (pastedNullComparison X).ofLevels _ _ (originalOldNull_level X) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level X n

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluationNull
