/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.FiniteLoopWords
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.KTheory.Bass.LoopStrengthTranspose

/-!
# The fixed loop words through every finite Bass strength

The original iterated strength evaluates as the Bass image of the complete finite evaluation
map. Hence the specified cyclic and reversal words commute with it as actual natural
transformations. The residual Bass value, including its independent original loop time,
is never included in the permuted tuple. No cone-block interchange is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.FiniteLoopStrengthWords
open FiniteConeStrength LoopStrengthTranspose
open IteratedLoopStrength FiniteLoopWords
variable {C : Type u} [Category.{v} C]

/-- The actual natural transformation evaluating the whole prescribed finite loop tuple. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean:32"
  "adaptation" "Original strength evaluation, naturality and full casts."]
def evaluationTuple : ∀ (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}),
    (Fin j → unitInterval) → (loopDiagram j F ⟶ F)
  | 0, F, _ => 𝟙 F
  | j + 1, F, t => evaluationAt (loopDiagram j F) (t 0) ≫
      evaluationTuple j F (Fin.tail t)

/-- The bundled evaluation map has exactly the original iterated pointwise value. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean:39"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem evaluationTuple_apply (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : ((loopDiagram j F).obj X).space n) (t : Fin j → unitInterval) :
    ((evaluationTuple j F t).app X).map n z = evaluate j F X n z t := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih (Path.toContinuousMap z (t 0)) (Fin.tail t)

/-- Reversal exchanges precisely the prescribed evaluation tuple. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean:47"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem reversal_evaluationTuple (j : ℕ) (F : C ⥤ LoopPrespectrum.{w})
    (t : Fin j → unitInterval) :
    (reversalIso j F).hom ≫ evaluationTuple j F t = evaluationTuple j F (t ∘ Fin.rev) := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  change ((evaluationTuple j F t).app X).map n
    (((reversalIso j F).hom.app X).map n z) = _
  rw [evaluationTuple_apply, reversalIso_evaluate, evaluationTuple_apply]

/-- The fixed cyclic word moves the first evaluation coordinate to the last. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean:61"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem cyclic_evaluationTuple (i : ℕ) (F : C ⥤ LoopPrespectrum.{w})
    (t : Fin (i + 1) → unitInterval) :
    (cyclicIso i F).hom ≫ evaluationTuple (i + 1) F t =
      evaluationTuple (i + 1) F (Fin.snoc (Fin.tail t) (t 0)) := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  change ((evaluationTuple (i + 1) F t).app X).map n
    (((cyclicIso i F).hom.app X).map n z) = _
  rw [evaluationTuple_apply, cyclicIso_evaluate, evaluationTuple_apply]

/-- Every finite strength retains the complete Bass value after all input evaluations. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean:76"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem iteratedStrength_evaluation (Q : C ⥤ Arrow (Arrow C)) (j : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : (((strictDiagramFunctor Q).obj (loopDiagram j F)).obj X).space n)
    (t : Fin j → unitInterval) :
    evaluate j ((strictDiagramFunctor Q).obj F) X n
      (((iteratedStrength Q j F).app X).map n z) t =
      (((strictDiagramFunctor Q).map (evaluationTuple j F t)).app X).map n z := by
  induction j with
  | zero =>
    exact (congrArg (fun a => (a.app X).map n z)
      ((strictDiagramFunctor Q).map_id F)).symm
  | succ j ih =>
    change evaluate j ((strictDiagramFunctor Q).obj F) X n
      (((iteratedStrength Q j F).app X).map n
        (Path.toContinuousMap ((LoopStrength.strength Q (loopDiagram j F) X).map n z)
          (t 0))) (Fin.tail t) = _
    rw [ih]
    have h := strength_evaluation Q (loopDiagram j F) X n (t 0) z
    refine (congrArg (fun y => (((strictDiagramFunctor Q).map
      (evaluationTuple j F (Fin.tail t))).app X).map n y) h).trans ?_
    exact (congrArg (fun a => (a.app X).map n z)
      ((strictDiagramFunctor Q).map_comp (evaluationAt (loopDiagram j F) (t 0))
        (evaluationTuple j F (Fin.tail t)))).symm

/-- The full fixed finite strength commutes with reversal of all input-loop coordinates. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean:101"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem iteratedStrength_reversal (Q : C ⥤ Arrow (Arrow C)) (j : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).map (reversalIso j F).hom ≫ iteratedStrength Q j F =
      iteratedStrength Q j F ≫ (reversalIso j ((strictDiagramFunctor Q).obj F)).hom := by
  apply evaluation_hom_ext j
  intro X n z t
  change evaluate j ((strictDiagramFunctor Q).obj F) X n
    (((iteratedStrength Q j F).app X).map n
      ((((strictDiagramFunctor Q).map (reversalIso j F).hom).app X).map n z)) t =
    evaluate j ((strictDiagramFunctor Q).obj F) X n
      (((reversalIso j ((strictDiagramFunctor Q).obj F)).hom.app X).map n
        (((iteratedStrength Q j F).app X).map n z)) t
  rw [iteratedStrength_evaluation, reversalIso_evaluate, iteratedStrength_evaluation]
  have h := congrArg (fun a => (a.app X).map n z)
    ((strictDiagramFunctor Q).map_comp (reversalIso j F).hom (evaluationTuple j F t))
  rw [reversal_evaluationTuple] at h
  exact h.symm

/-- The full fixed finite strength also commutes with its specified cyclic input word. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean:120"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem iteratedStrength_cyclic (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).map (cyclicIso i F).hom ≫ iteratedStrength Q (i + 1) F =
      iteratedStrength Q (i + 1) F ≫
        (cyclicIso i ((strictDiagramFunctor Q).obj F)).hom := by
  apply evaluation_hom_ext (i + 1)
  intro X n z t
  change evaluate (i + 1) ((strictDiagramFunctor Q).obj F) X n
    (((iteratedStrength Q (i + 1) F).app X).map n
      ((((strictDiagramFunctor Q).map (cyclicIso i F).hom).app X).map n z)) t =
    evaluate (i + 1) ((strictDiagramFunctor Q).obj F) X n
      (((cyclicIso i ((strictDiagramFunctor Q).obj F)).hom.app X).map n
        (((iteratedStrength Q (i + 1) F).app X).map n z)) t
  rw [iteratedStrength_evaluation, cyclicIso_evaluate, iteratedStrength_evaluation]
  have h := congrArg (fun a => (a.app X).map n z)
    ((strictDiagramFunctor Q).map_comp (cyclicIso i F).hom (evaluationTuple (i + 1) F t))
  rw [cyclic_evaluationTuple] at h
  exact h.symm

end KTheory.Bass.FiniteLoopStrengthWords
