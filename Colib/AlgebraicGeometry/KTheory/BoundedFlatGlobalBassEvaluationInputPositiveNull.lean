/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputPositiveSupport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationNull
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Colib.Topology.Prespectrum.RelativeHomotopyPostcompReparam

/-!
# Actual positive-cone factors of the original evaluation null comparison

The original strict source null and the complete chosen evaluation null recipe live in the
actual positive cones. Their strict inclusions preserve every original chart movement,
cone interchange, boundary collapse and associator at the same independent parameters.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositive
open GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- Strict positive composition is the original Laurent projection. -/
theorem strictChart_projection :
    sectionMap (projection.app X) ≫ strictChart X =
      sectionMap (GlobalRawBass.laurentProjection.app X) := by
  rw [← sectionMap_comp, GlobalRawBass.plus_projection]

/-- The original strict source-null cylinder already lives in the actual positive cone. -/
def strictSourceNull :
    Homotopy (sectionMap (GlobalRawBass.laurentProjection.app X) ≫
      mappingConeInclusion (strictChart X))
      (zeroHom (sectionDiagram.obj (Opposite.op X))
        (mappingCone (strictChart X))) :=
  (Homotopy.precomp (sectionMap (projection.app X))
    (mappingConeHomotopy (strictChart X))).cast
      (by rw [← Category.assoc, strictChart_projection])
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        rfl)

/-- Strict inclusion preserves every original source-null cylinder coordinate. -/
theorem strictSourceNull_factor (n : ℕ) :
    ((strictSourceNull X).postcomp (strictInclusion X)).level n =
      (GlobalBassEvaluation.strictSourceNull X).level n := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositive

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositiveNull
open GlobalBassEvaluation GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- Original positive chart evaluation, with only its strict starting equality transported. -/
def positiveMovement :=
  (chartFirstTrack X (plus.app X) (GlobalRawBass.plus_projection X)).postcomp
    (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))

/-- The original polynomial evaluation track followed by the raw positive Laurent leg. -/
def polynomialMovement :=
  (chartSecondTrack X (plus.app X)).postcomp
    (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))

/-- The unchanged Laurent coefficient evaluation track followed by raw cone inclusion. -/
def laurentMovement :=
  (evaluationComparison (GlobalRawBass.laurentProjection.app X)).postcomp
    (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))

/-- Original raw positive composition, preceded by the original base evaluation. -/
def newPositive :=
  ((Homotopy.precomp (evaluation X)
    (GlobalRawBass.plusHomotopy X)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))

/-- The actual positive-chart geometric equation retains its whole cone image. -/
def positivePasting :
    ((positiveMovement X).trans (polynomialMovement X)).RelHomotopy
      ((laurentMovement X).trans (newPositive X)) := by
  refine ((chartPasting X (plus.app X) (GlobalRawBass.plus_projection X)).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).ofLevels _ _ ?_ ?_
  · intro n
    rw [Homotopy.postcomp_trans]
    rfl
  · intro n
    rw [chartOuterTrack, Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr
    · rfl
    · rfl

/-- The evaluated strict source leg traverses the original raw cone cylinder. -/
def oldCone : Homotopy
    (((sectionMap (projection.app X) ≫
      evaluation (polynomial.obj X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
          mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)) (zeroHom _ _) :=
  (Homotopy.precomp (sectionMap (projection.app X) ≫
    evaluation (polynomial.obj X))
    (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).cast
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        rfl) rfl

/-- The base evaluation followed by the raw source leg traverses that same cone cylinder. -/
def newCone : Homotopy
    (((evaluation X ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
          mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)) (zeroHom _ _) :=
  (Homotopy.precomp (evaluation X ≫
    boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).cast
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
    (zeroHom (sectionDiagram.obj (Opposite.op X))
      (mappingCone (GlobalRawBass.InputIdentityPositive.chart X)))
  have J : (oldCone X).RelHomotopy
      (((polynomialMovement X).trans (newCone X)).trans Z) := by
    refine ((Homotopy.Square.interchange (evaluationComparison (projection.app X))
      (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).toBoundary).ofLevels
        _ _ ?_ ?_
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
def originalOldNull : Homotopy
    ((sectionMap (GlobalRawBass.laurentProjection.app X) ≫
      evaluation (laurent.obj X)) ≫
        mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)) (zeroHom _ _) :=
  ((InputPositive.strictSourceNull X).postcomp
    (InputPositive.evaluation X)).cast
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        rfl)
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        exact (InputPositive.evaluation X).map_point n)

/-- The unchanged raw nullhomotopy preceded by the actual original base evaluation. -/
def originalNewNull : Homotopy
    ((evaluation X ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (GlobalRawBass.laurentProjection.app X)) ≫
        mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)) (zeroHom _ _) :=
  (Homotopy.precomp (evaluation X)
    (GlobalRawBass.InputIdentityPositive.sourceNull X)).cast (Category.assoc _ _ _).symm rfl

/-- Every original raw-null coordinate retains its positive track and actual cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull X).level n = ((newPositive X).trans (newCone X)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (evaluation X)
    ((GlobalRawBass.plusHomotopy X).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)))).trans
      (Homotopy.precomp (evaluation X)
        (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

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


/-- Strict positive inclusion preserves the complete positive chart evaluation. -/
theorem positiveMovement_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (positiveMovement X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.positiveMovement X) := by
  intro s
  rfl

/-- Strict positive inclusion preserves the complete polynomial evaluation. -/
theorem polynomialMovement_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (polynomialMovement X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.polynomialMovement X) := by
  intro s
  rfl

/-- Strict positive inclusion preserves the complete Laurent evaluation. -/
theorem laurentMovement_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (laurentMovement X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.laurentMovement X) := by
  intro s
  rfl

/-- Strict positive inclusion preserves the complete original raw positive leg. -/
theorem newPositive_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (newPositive X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.newPositive X) := by
  intro s
  rfl

/-- Strict positive inclusion preserves the complete old cone cylinder. -/
theorem oldCone_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (oldCone X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.oldCone X) := by
  intro s
  rfl

/-- Strict positive inclusion preserves the complete new cone cylinder. -/
theorem newCone_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (newCone X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.newCone X) := by
  intro s
  rfl

/-- The chosen geometric chart pasting has its exact original full-cone image. -/
theorem positivePasting_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (positivePasting X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.positivePasting X) := by
  intro r s
  rfl

/-- The actual cone interchange and original three-sided collapse preserve both times. -/
theorem conePasting_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (conePasting X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.conePasting X) := by
  unfold conePasting GlobalBassEvaluationNull.conePasting
  apply Homotopy.RelHomotopy.MappedAt.trans
  · intro r s
    rfl
  · exact ((polynomialMovement_mapped X n x).trans (newCone_mapped X n x)).transRefl

/-- Every relative subdivision of the original pasted-null recipe is unchanged. -/
theorem pastedNullComparison_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (pastedNullComparison X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.pastedNullComparison X) := by
  have hA := positiveMovement_mapped X n x
  have hB := polynomialMovement_mapped X n x
  have hC := newCone_mapped X n x
  exact (hA.refl.hcomp (conePasting_mapped X n x)).trans
    ((hA.transAssoc hB hC).symm.trans
      (((positivePasting_mapped X n x).hcomp hC.refl).trans
        ((laurentMovement_mapped X n x).transAssoc (newPositive_mapped X n x) hC)))

/-- The original old null retains its entire positive movement and cylinder word. -/
theorem originalOldNull_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (originalOldNull X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.originalOldNull X) := by
  intro s
  rw [originalOldNull_level, GlobalBassEvaluationNull.originalOldNull_level]
  exact ((positiveMovement_mapped X n x).trans (oldCone_mapped X n x)) s

/-- The original new null retains its entire raw positive movement and cylinder word. -/
theorem originalNewNull_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (originalNewNull X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.originalNewNull X) := by
  intro s
  rw [originalNewNull_level, GlobalBassEvaluationNull.originalNewNull_level]
  exact ((newPositive_mapped X n x).trans (newCone_mapped X n x)) s

/-- The entire original null comparison factors without changing any chosen operation. -/
theorem originalNullComparison_mapped (n : ℕ)
    (x : (sectionDiagram.obj (Opposite.op X)).space n) :
    (originalNullComparison X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluationNull.originalNullComparison X) :=
  pastedNullComparison_mapped X n x

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositiveNull
