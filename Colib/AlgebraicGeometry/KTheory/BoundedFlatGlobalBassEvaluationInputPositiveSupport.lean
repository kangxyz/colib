/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCommutingSquare
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputConeSource
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveSupport
public import Colib.Topology.Prespectrum.ConeSquareMapMovingCoherence

/-!
# Actual positive-cone support for mixed global evaluation

The strict positive cone includes by its original polynomial span face, preserving every cone
height. Its evaluation uses the original positive evaluation comparison. Actual strict input
and the original raw positive input are compared using the original commuting geometric square,
with its strict source transport and its complete split raw path unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositive
open GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- The actual strict positive chart map. -/
abbrev strictChart := sectionMap (plus.app X)

/-- The original positive polynomial face and Laurent identity form a strict inclusion square. -/
def strictInclusionSquare :
    Arrow.mk (strictChart X) ⟶ Arrow.mk (StrictSquare.comparison (sectionSquare X)) :=
  Arrow.homMk
    (HomotopyPushout.inl (sectionMap (projection.app X)) (sectionMap (projection.app X)))
    (𝟙 _) (by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      rfl)

/-- Strict positive inclusion does not introduce a new path segment or change cone height. -/
def strictInclusion : mappingCone (strictChart X) ⟶
    mappingCone (StrictSquare.comparison (sectionSquare X)) :=
  mappingConeMap (strictInclusionSquare X)

/-- Laurent inclusion is literally preserved by the strict positive inclusion. -/
theorem strictInclusion_inclusion :
    mappingConeInclusion (strictChart X) ≫ strictInclusion X =
      mappingConeInclusion (StrictSquare.comparison (sectionSquare X)) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

/-- Every positive strict cylinder retains its original height and polynomial point. -/
theorem strictInclusion_cylinder (n : ℕ) (s : unitInterval)
    (x : (sectionDiagram.obj (op (polynomial.obj X))).space n) :
    (strictInclusion X).map n
      (ReducedMappingCone.cylinder _ _ ((strictChart X).map n) (s, x)) =
      ReducedMappingCone.cylinder _ _ ((StrictSquare.comparison (sectionSquare X)).map n)
        (s, (HomotopyPushout.inl (sectionMap (projection.app X))
          (sectionMap (projection.app X))).map n x) := rfl

/-- Actual positive evaluation is the square-cone map of the original positive comparison. -/
def evaluation : mappingCone (strictChart X) ⟶
    mappingCone (GlobalRawBass.InputIdentityPositive.chart X) :=
  mappingConeSquareMap (strictChart X) (GlobalRawBass.InputIdentityPositive.chart X)
    (GlobalBassEvaluation.evaluation (polynomial.obj X))
    (GlobalBassEvaluation.evaluation (laurent.obj X)) (evaluationComparison (plus.app X))

/-- Both original evaluation null halves map to the unchanged whole evaluation null. -/
theorem evaluationNull_factor (n : ℕ) :
    ((mappingConeSquareNullHomotopy (strictChart X)
      (GlobalRawBass.InputIdentityPositive.chart X)
      (GlobalBassEvaluation.evaluation (polynomial.obj X))
      (GlobalBassEvaluation.evaluation (laurent.obj X))
      (evaluationComparison (plus.app X))).postcomp
        (GlobalRawBass.InputIdentityPositive.inclusion X)).level n =
    (Homotopy.precomp
      (HomotopyPushout.inl (sectionMap (projection.app X)) (sectionMap (projection.app X)))
      (mappingConeSquareNullHomotopy (StrictSquare.comparison (sectionSquare X))
        (GlobalRawBass.comparison X) (spanEvaluation X)
        (GlobalBassEvaluation.evaluation (laurent.obj X)) (comparisonHomotopy X))).level n := by
  simp only [mappingConeSquareNullHomotopy, Homotopy.postcomp_trans, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

/-- The actual positive evaluation factors the fixed whole evaluation on every cone point. -/
theorem evaluation_factor :
    evaluation X ≫ GlobalRawBass.InputIdentityPositive.inclusion X =
      strictInclusion X ≫ coneEvaluation X := by
  apply mappingCone_hom_ext
  · apply Topology.LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  · intro n s x
    exact DFunLike.congr_fun (evaluationNull_factor X n) (s, x)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual strict positive naturality square comes from geometric positive naturality. -/
def strictInputSquare : Arrow.mk (strictChart Y) ⟶ Arrow.mk (strictChart X) :=
  Arrow.homMk (sectionMap (polynomial.map g)) (sectionMap (laurent.map g)) (by
    change sectionMap (polynomial.map g) ≫ sectionMap (plus.app X) =
      sectionMap (plus.app Y) ≫ sectionMap (laurent.map g)
    rw [← sectionMap_comp, ← sectionMap_comp, plus.naturality g])

/-- Actual strict positive input uses the strict cone functor without an added constant half. -/
def strictInput : mappingCone (strictChart Y) ⟶ mappingCone (strictChart X) :=
  mappingConeMap (strictInputSquare g)

/-- Strict input preserves the entire original positive support. -/
theorem strictInput_factor :
    strictInput g ≫ strictInclusion X =
      strictInclusion Y ≫ InputConeSource.strictConeMap g := by
  apply mappingCone_hom_ext
  · apply Topology.LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  · intro n s x
    rfl

/-- The source is the original X positive comparison under the actual strict input square. -/
def source :=
  mappingConeSquareStrictPrecompTrack (strictChart Y) (strictChart X)
    (GlobalRawBass.InputIdentityPositive.chart X) (strictInputSquare g)
    (GlobalBassEvaluation.evaluation (polynomial.obj X))
    (GlobalBassEvaluation.evaluation (laurent.obj X)) (evaluationComparison (plus.app X))

/-- The positive target retains the original evaluation and split raw positive square paths. -/
def target :=
  coneSquarePastedHomotopy (strictChart Y) (GlobalRawBass.InputIdentityPositive.chart Y)
    (GlobalRawBass.InputIdentityPositive.chart X)
    (GlobalBassEvaluation.evaluation (polynomial.obj Y))
    (GlobalBassEvaluation.evaluation (laurent.obj Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (evaluationComparison (plus.app Y)) (GlobalRawBass.plusSquareHomotopy g)

/-- The positive mixed square is the selected original commuting square with endpoint casts only. -/
def square : (source g).Square (target g)
    (Homotopy.precomp (strictChart Y) (evaluationComparison (laurent.map g)))
    ((evaluationComparison (polynomial.map g)).postcomp
      (GlobalRawBass.InputIdentityPositive.chart X)) := by
  apply (InputCommutingSquare.square (laurent.map g) (plus.app Y)
    (plus.app X) (polynomial.map g) (plus.naturality g)).ofBoundaryLevels
  · intro n
    rfl
  · intro n
    unfold target coneSquarePastedHomotopy
    rw [Homotopy.cast_level]
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rfl
  · intro n
    rfl

/-- The unchanged positive mixed square retains both original square coordinates. -/
theorem square_level (n : ℕ) :
    (square g).level n =
      (InputCommutingSquare.square (laurent.map g) (plus.app Y)
        (plus.app X) (polynomial.map g) (plus.naturality g)).level n := rfl

/-- The direct positive cone map uses the actual strict-precomposed source track. -/
def directConeMap :=
  mappingConeSquareMap (strictChart Y) (GlobalRawBass.InputIdentityPositive.chart X)
    (sectionMap (polynomial.map g) ≫ GlobalBassEvaluation.evaluation (polynomial.obj X))
    (sectionMap (laurent.map g) ≫ GlobalBassEvaluation.evaluation (laurent.obj X)) (source g)

/-- Strict positive precomposition is exactly the direct original square-cone map. -/
theorem strict_comp_evaluation : strictInput g ≫ evaluation X = directConeMap g :=
  mappingConeMap_comp_squareMap (strictChart Y) (strictChart X)
    (GlobalRawBass.InputIdentityPositive.chart X) (strictInputSquare g)
    (GlobalBassEvaluation.evaluation (polynomial.obj X))
    (GlobalBassEvaluation.evaluation (laurent.obj X)) (evaluationComparison (plus.app X))

/-- The whole positive moving null square keeps the original null-surface word and all clocks. -/
def nullSquare :=
  coneSquareCompositionMovingNullSquare (strictChart Y)
    (GlobalRawBass.InputIdentityPositive.chart Y) (GlobalRawBass.InputIdentityPositive.chart X)
    (GlobalBassEvaluation.evaluation (polynomial.obj Y))
    (GlobalBassEvaluation.evaluation (laurent.obj Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (evaluationComparison (plus.app Y)) (GlobalRawBass.plusSquareHomotopy g)
    (source g) (evaluationComparison (polynomial.map g))
    (evaluationComparison (laurent.map g)) (square g)

/-- The actual positive mixed comparison supplies its direct-to-composite cone homotopy. -/
def directConeHomotopy : Homotopy (directConeMap g)
    (evaluation Y ≫ GlobalRawBass.InputIdentityPositive.coneMap g) :=
  coneSquareCompositionHomotopyOfSquare (strictChart Y)
    (GlobalRawBass.InputIdentityPositive.chart Y) (GlobalRawBass.InputIdentityPositive.chart X)
    (GlobalBassEvaluation.evaluation (polynomial.obj Y))
    (GlobalBassEvaluation.evaluation (laurent.obj Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (evaluationComparison (plus.app Y)) (GlobalRawBass.plusSquareHomotopy g)
    (source g) (evaluationComparison (polynomial.map g))
    (evaluationComparison (laurent.map g)) (square g)

/-- Positive mixed input naturality compares the actual strict and raw positive composites. -/
def coneHomotopy : Homotopy (strictInput g ≫ evaluation X)
    (evaluation Y ≫ GlobalRawBass.InputIdentityPositive.coneMap g) :=
  (directConeHomotopy g).cast (strict_comp_evaluation g).symm rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputPositive
