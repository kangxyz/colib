/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.IteratedLoopStrength
public import Colib.KTheory.Bass.FiniteConeStrength
public import Colib.Topology.Prespectrum.LoopTranspose

/-!
# The original double-loop transpose through two Bass strengths

The fixed twofold strength retains the two input-loop evaluation times and the
independent original Bass loop. Its full map commutes with transposing the two
input coordinates. The proof uses the original evaluation time slices and
functoriality, without a geometric cone permutation or a braid assumption.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.LoopStrengthTranspose
open LoopStrength FiniteConeStrength IteratedLoopStrength
variable {C : Type u} [Category.{v} C]

/-- The original evaluation at a specified parameter is an actual natural transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthTranspose.lean:29"
  "adaptation" "Original strength evaluation, naturality and full casts."]
def evaluationAt (F : C ⥤ LoopPrespectrum.{w}) (r : unitInterval) :
    (F ⋙ parameterLoopingFunctor) ⟶ F :=
  diagramHomotopyAt (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
    (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
    (evaluation F) (evaluation_naturality F) r

/-- Evaluate both original loop coordinates in their given order. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthTranspose.lean:36"
  "adaptation" "Original strength evaluation, naturality and full casts."]
def evaluationTwo (F : C ⥤ LoopPrespectrum.{w}) (r s : unitInterval) :
    ((F ⋙ parameterLoopingFunctor) ⋙ parameterLoopingFunctor) ⟶ F :=
  evaluationAt (F ⋙ parameterLoopingFunctor) r ≫ evaluationAt F s

/-- The pointwise original transpose is natural in every coefficient arrow. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthTranspose.lean:41"
  "adaptation" "Original strength evaluation, naturality and full casts."]
def transposeDiagram (F : C ⥤ LoopPrespectrum.{w}) :
    ((F ⋙ parameterLoopingFunctor) ⋙ parameterLoopingFunctor) ⟶
      ((F ⋙ parameterLoopingFunctor) ⋙ parameterLoopingFunctor) where
  app X := LoopTranspose.transpose (F.obj X)
  naturality {_X _Y} f := LoopTranspose.naturality (F.map f)

/-- Transposition exchanges precisely the two evaluation times. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthTranspose.lean:48"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem transpose_evaluationTwo (F : C ⥤ LoopPrespectrum.{w})
    (r s : unitInterval) :
    transposeDiagram F ≫ evaluationTwo F r s = evaluationTwo F s r := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  rfl

/-- The unchanged strength evaluated at a loop time is the Bass image of evaluation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthTranspose.lean:60"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem strength_evaluation (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ) (r : unitInterval)
    (z : (((strictDiagramFunctor Q).obj (F ⋙ parameterLoopingFunctor)).obj X).space n) :
    Path.toContinuousMap ((strength Q F X).map n z) r =
      (((strictDiagramFunctor Q).map (evaluationAt F r)).app X).map n z :=
  bassHomotopy_apply (E := F ⋙ parameterLoopingFunctor) (F := F)
    (evaluation F) (evaluation_naturality F) Q X n r z

/-- Two strengths preserve the entire remaining Bass value after both evaluations. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthTranspose.lean:69"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem iteratedStrength_two_evaluation (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ) (r s : unitInterval)
    (z : (((strictDiagramFunctor Q).obj
      ((F ⋙ parameterLoopingFunctor) ⋙ parameterLoopingFunctor)).obj X).space n) :
    Path.toContinuousMap (Path.toContinuousMap
        (((iteratedStrength Q 2 F).app X).map n z) r) s =
      (((strictDiagramFunctor Q).map (evaluationTwo F r s)).app X).map n z := by
  change Path.toContinuousMap ((strength Q F X).map n
    (Path.toContinuousMap ((strength Q (F ⋙ parameterLoopingFunctor) X).map n z) r)) s = _
  have h₁ := strength_evaluation Q F X n s
    (Path.toContinuousMap ((strength Q (F ⋙ parameterLoopingFunctor) X).map n z) r)
  have h₂ := strength_evaluation Q (F ⋙ parameterLoopingFunctor) X n r z
  refine h₁.trans ((congrArg
    (fun x => (((strictDiagramFunctor Q).map (evaluationAt F s)).app X).map n x)
    h₂).trans ?_)
  exact (congrArg (fun a => (a.app X).map n z)
    ((strictDiagramFunctor Q).map_comp (evaluationAt (F ⋙ parameterLoopingFunctor) r)
      (evaluationAt F s))).symm

/-- The full twofold strength commutes with the original input-coordinate transpose. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthTranspose.lean:89"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem iteratedStrength_two_transpose (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).map (transposeDiagram F) ≫ iteratedStrength Q 2 F =
      iteratedStrength Q 2 F ≫ transposeDiagram ((strictDiagramFunctor Q).obj F) := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext r
  apply Path.ext
  funext s
  change Path.toContinuousMap (Path.toContinuousMap
      (((iteratedStrength Q 2 F).app X).map n
        ((((strictDiagramFunctor Q).map (transposeDiagram F)).app X).map n z)) r) s =
    Path.toContinuousMap (Path.toContinuousMap
      (((iteratedStrength Q 2 F).app X).map n z) s) r
  rw [iteratedStrength_two_evaluation, iteratedStrength_two_evaluation]
  have h := congrArg (fun a => (a.app X).map n z)
    ((strictDiagramFunctor Q).map_comp (transposeDiagram F) (evaluationTwo F r s))
  rw [transpose_evaluationTwo] at h
  exact h.symm

end KTheory.Bass.LoopStrengthTranspose
