/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputPositiveNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationUnitPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyPostcompConjugation
public import Colib.Topology.Prespectrum.RelativeHomotopyLoop
public import Colib.Topology.Prespectrum.NullLoopNaturality

/-!
# The exact positive-cone factor of the chosen global evaluation seed homotopy

The original strict unit and source null give the supported strict seed. The complete original
unit/null pasting and conjugation recipe is performed in the actual positive raw cone; strict
inclusion recovers the frozen seed homotopy at every degree and both independent times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositive
open GlobalSectionChangeIndex InputPositiveNull
variable (X : Scheme.{u})

/-- The original global Laurent-unit seed uses its actual strict source-null cylinder. -/
def strictSeed : sectionDiagram.obj (op X) ⟶
    parameterLooping (mappingCone (strictChart X)) :=
  ((strictLaurentTrack (op X)).postcomp
    (mappingConeInclusion (strictChart X))).nullLoopMap
      (strictSourceNull X)

/-- The actual strict positive seed maps exactly to the frozen whole strict seed. -/
theorem strictSeed_factor :
    strictSeed X ≫ parameterLoopingMap (strictInclusion X) =
      GlobalBassEvaluation.strictSeed X := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 (sectionDiagram.obj (op X))) (strictInclusion X)
    ((strictLaurentTrack (op X)).postcomp
      (mappingConeInclusion (strictChart X)))
    ((strictLaurentTrack (op X)).postcomp
      (mappingConeInclusion (StrictSquare.comparison (sectionSquare X))))
    (strictSourceNull X) (GlobalBassEvaluation.strictSourceNull X)
    (fun _ ↦ rfl) (strictSourceNull_factor X)
  simpa only [Category.id_comp, strictSeed, GlobalBassEvaluation.strictSeed] using h

/-- The original strict unit evaluated into the actual raw cone. -/
def oldUnit :=
  (evaluationOldUnit (GlobalRawBass.laurentProjection.app X)
    (laurentScalar (op X))).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))

/-- Original base evaluation followed by the original raw forward unit in the same cone. -/
def newUnit :=
  (evaluationNewUnit (GlobalRawBass.laurentProjection.app X)
    (laurentScalar (op X))).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))

/-- The independently constructed unit pasting retains both complete original cone-unit tracks. -/
def unitPasting :
    ((oldUnit X).trans (laurentMovement X)).RelHomotopy
      ((laurentMovement X).trans (newUnit X)) := by
  apply ((globalLaurentEvaluationPasting (op X)).postcomp
    (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).ofLevels
  · intro n
    rw [Homotopy.postcomp_trans]
    rfl
  · intro n
    rw [Homotopy.postcomp_trans]
    rfl

/-- Original unit and source-null pastings compare the actual based Laurent conjugates. -/
def conjugation :
    ((oldUnit X).conjugateToZero (originalOldNull X)).RelHomotopy
      ((newUnit X).conjugateToZero (originalNewNull X)) :=
  Homotopy.RelHomotopy.conjugateNaturality (laurentMovement X)
    (oldUnit X) (newUnit X) (originalOldNull X) (originalNewNull X)
    (unitPasting X) (originalNullComparison X)

/-- The initial conjugate is precisely the original strict seed followed by actual evaluation. -/
theorem originalStrictSeed :
    (oldUnit X).nullLoopMap (originalOldNull X) =
      strictSeed X ≫ parameterLoopingMap (evaluation X) := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 (sectionDiagram.obj (op X))) (evaluation X)
    ((strictLaurentTrack (op X)).postcomp
      (mappingConeInclusion (strictChart X)))
    (oldUnit X) (strictSourceNull X) (originalOldNull X)
    (by intro n; rfl) (by intro n; rfl)
  exact h.symm

/-- The final conjugate is precisely evaluation followed by the unchanged raw Laurent seed. -/
theorem originalRawSeed :
    (newUnit X).nullLoopMap (originalNewNull X) =
      GlobalBassEvaluation.evaluation X ≫ GlobalRawBass.InputIdentityPositive.seed X := by
  have h := Homotopy.nullLoopMap_naturality (GlobalBassEvaluation.evaluation X)
    (𝟙 (mappingCone (GlobalRawBass.InputIdentityPositive.chart X))) (newUnit X)
    ((GlobalRawBass.unitHomotopy X).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)))
    (originalNewNull X) (GlobalRawBass.InputIdentityPositive.sourceNull X)
    (by intro n; rfl) (by intro n; rfl)
  exact h

/-- The actual one-step evaluation intertwines the two original forward Laurent seeds. -/
def seedHomotopy : Homotopy (strictSeed X ≫ parameterLoopingMap (evaluation X))
    (GlobalBassEvaluation.evaluation X ≫ GlobalRawBass.InputIdentityPositive.seed X) :=
  (conjugation X).zeroLoopMapHomotopy.cast (originalStrictSeed X) (originalRawSeed X)

/-- Comparison and output-loop times remain independent at every original source point. -/
theorem seedHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (sectionDiagram.obj (op X)).space n) :
    Path.toContinuousMap ((seedHomotopy X).level n (r, x)) s =
      (conjugation X).level n (r, (s, x)) := rfl


/-- Strict positive inclusion preserves the original evaluated strict unit loop. -/
theorem oldUnit_mapped (n : ℕ)
    (x : (sectionDiagram.obj (op X)).space n) :
    (oldUnit X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluation.oldUnit X) := by
  intro s
  rfl

/-- Strict positive inclusion preserves the original evaluated raw unit loop. -/
theorem newUnit_mapped (n : ℕ)
    (x : (sectionDiagram.obj (op X)).space n) :
    (newUnit X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluation.newUnit X) := by
  intro s
  rfl

/-- The supplied original unit pasting retains both exact independent coordinates. -/
theorem unitPasting_mapped (n : ℕ)
    (x : (sectionDiagram.obj (op X)).space n) :
    (unitPasting X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluation.unitPasting X) := by
  intro r s
  rfl

/-- Every operation in the frozen conjugate-naturality recipe has its exact positive image. -/
theorem conjugation_mapped (n : ℕ)
    (x : (sectionDiagram.obj (op X)).space n) :
    (conjugation X).MappedAt (GlobalRawBass.InputIdentityPositive.inclusion X) n x
      (GlobalBassEvaluation.conjugation X) := by
  apply Homotopy.RelHomotopy.conjugateNaturality_mapped
  · exact InputPositiveNull.laurentMovement_mapped X n x
  · exact oldUnit_mapped X n x
  · exact newUnit_mapped X n x
  · exact InputPositiveNull.originalNewNull_mapped X n x
  · exact unitPasting_mapped X n x
  · exact InputPositiveNull.originalNullComparison_mapped X n x

/-- The entire selected original seed homotopy factors at every degree, comparison time,
output-loop time and original source point. No unit, null or pasting has been replaced. -/
theorem seedHomotopy_factor (n : ℕ) (r s : unitInterval)
    (x : (sectionDiagram.obj (op X)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (Path.toContinuousMap ((seedHomotopy X).level n (r, x)) s) =
      Path.toContinuousMap ((GlobalBassEvaluation.seedHomotopy X).level n (r, x)) s :=
  conjugation_mapped X n x r s

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositive
