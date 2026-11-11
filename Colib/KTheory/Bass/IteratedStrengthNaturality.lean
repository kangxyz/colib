/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.FiniteLoopStrengthWords

/-! # Naturality of the unchanged finite Bass strength -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.IteratedStrengthNaturality
open FiniteConeStrength IteratedLoopStrength
open FiniteLoopWords FiniteLoopStrengthWords
variable {C : Type u} [Category.{v} C]

/-- Finite evaluation is natural as a complete map of coefficient diagrams. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedStrengthNaturality.lean:23"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem evaluationTuple_naturality (j : ℕ) {F G : C ⥤ LoopPrespectrum.{w}}
    (f : F ⟶ G) (t : Fin j → unitInterval) :
    loopMap j f ≫ evaluationTuple j G t = evaluationTuple j F t ≫ f := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  change ((evaluationTuple j G t).app X).map n (((loopMap j f).app X).map n z) =
    (f.app X).map n (((evaluationTuple j F t).app X).map n z)
  rw [evaluationTuple_apply, evaluationTuple_apply, evaluate_loopMap]

/-- Every finite original strength is natural in an arbitrary diagram map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedStrengthNaturality.lean:37"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem iteratedStrength_naturality (Q : C ⥤ Arrow (Arrow C)) (j : ℕ)
    {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G) :
    (strictDiagramFunctor Q).map (loopMap j f) ≫ iteratedStrength Q j G =
      iteratedStrength Q j F ≫ loopMap j ((strictDiagramFunctor Q).map f) := by
  apply evaluation_hom_ext j
  intro X n z t
  change evaluate j ((strictDiagramFunctor Q).obj G) X n
      (((iteratedStrength Q j G).app X).map n
        ((((strictDiagramFunctor Q).map (loopMap j f)).app X).map n z)) t =
    evaluate j ((strictDiagramFunctor Q).obj G) X n
      (((loopMap j ((strictDiagramFunctor Q).map f)).app X).map n
        (((iteratedStrength Q j F).app X).map n z)) t
  rw [iteratedStrength_evaluation, evaluate_loopMap, iteratedStrength_evaluation]
  have h := congrArg (fun a => (a.app X).map n z)
    (congrArg (strictDiagramFunctor Q).map (evaluationTuple_naturality j f t))
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The single original strength is the one-step specialization of the finite naturality. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedStrengthNaturality.lean:56"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem strengthDiagram_naturality (Q : C ⥤ Arrow (Arrow C))
    {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G) :
    (strictDiagramFunctor Q).map (Functor.whiskerRight f parameterLoopingFunctor) ≫
        strengthDiagram Q G =
      strengthDiagram Q F ≫
        Functor.whiskerRight ((strictDiagramFunctor Q).map f) parameterLoopingFunctor := by
  simpa only [iteratedStrength, loopMap, loopDiagram, Functor.whiskerRight_id', Category.comp_id]
    using iteratedStrength_naturality Q 1 f

end KTheory.Bass.IteratedStrengthNaturality
