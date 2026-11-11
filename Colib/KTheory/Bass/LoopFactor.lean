/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.LoopStrength
public import Colib.Topology.Prespectrum.PushoutLooping
public import Colib.Topology.Prespectrum.ConeParameterLooping

/-!
# Reconstructed factorization through the actual cone-loop comparison

This independent prototype retains every pushout, cone and loop coordinate. This is an adopted
independent reconstruction; its bytes are not the historical checked source.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.LoopFactor

/-- Apply the original looping functor to all four corners. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactor.lean:28"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def loopSquare (S : Arrow (Arrow LoopPrespectrum.{w})) :
    Arrow (Arrow LoopPrespectrum.{w}) := parameterLoopingFunctor.mapArrow.mapArrow.obj S

/-- The actual span comparison commutes with pointwise looping. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactor.lean:32"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem span_square (S : Arrow (Arrow LoopPrespectrum.{w})) :
    HomotopyPushout.Looping.comparison S.left.hom S.hom.left ≫
        parameterLoopingMap (StrictSquare.comparison S) =
      StrictSquare.comparison (loopSquare S) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext t
  induction z using Quot.inductionOn with
  | h z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl

/-- The forward cone strength uses the actual pushout comparison and original cone descent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactor.lean:49"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def coneStrength (S : Arrow (Arrow LoopPrespectrum.{w})) :
    mappingCone (StrictSquare.comparison (loopSquare S)) ⟶
      parameterLooping (mappingCone (StrictSquare.comparison S)) :=
  mappingConeMap (Arrow.homMk
    (f := Arrow.mk (StrictSquare.comparison (loopSquare S)))
    (g := Arrow.mk (parameterLoopingMap (StrictSquare.comparison S)))
    (HomotopyPushout.Looping.comparison S.left.hom S.hom.left)
    (𝟙 _) (by simpa using (span_square S))) ≫
      mappingConeParameterLoopingComparison (StrictSquare.comparison S)

variable {C : Type u} [Category.{v} C]

/-- On every original cone cell the strength is the evaluation-family cone homotopy. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactor.lean:62"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem coneStrength_value (F : C ⥤ LoopPrespectrum.{w})
    (Q : C ⥤ Arrow (Arrow C)) (X : C) (n : ℕ) (r : unitInterval)
    (z : (mappingCone (StrictSquare.comparison
      (loopSquare (F.mapArrow.mapArrow.obj (Q.obj X))))).space n) :
    Path.toContinuousMap ((coneStrength (F.mapArrow.mapArrow.obj (Q.obj X))).map n z) r =
      (diagramSquareMapHomotopy
        (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
        (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
        (LoopStrength.evaluation F)
        (LoopStrength.evaluation_naturality F) (Q.obj X)).cone.level n (r, z) := by
  induction z using Quot.inductionOn with
  | h z =>
    cases z with
    | inl z => rfl
    | inr z =>
      rcases z with ⟨s, z⟩
      induction z using Quot.inductionOn with
      | h z =>
        cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl

/-- The whole original Bass strength factors with an explicit final loop transpose. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopFactor.lean:85"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem strength_factor_value (F : C ⥤ LoopPrespectrum.{w})
    (Q : C ⥤ Arrow (Arrow C)) (X : C) (n : ℕ)
    (γ : (((strictDiagramFunctor Q).obj (F ⋙ parameterLoopingFunctor)).obj X).space n)
    (r t : unitInterval) :
    Path.toContinuousMap
      (Path.toContinuousMap ((LoopStrength.strength Q F X).map n γ) r) t =
      Path.toContinuousMap (Path.toContinuousMap ((parameterLoopingMap
        (coneStrength (F.mapArrow.mapArrow.obj (Q.obj X)))).map n γ) t) r := by
  exact (coneStrength_value F Q X n r (Path.toContinuousMap γ t)).symm

end KTheory.Bass.LoopFactor
