/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.LoopConeTrack
public import Colib.Topology.Prespectrum.LoopTranspose

/-! # Whole-time loop strength for the original inverse-indexed cone action -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.LoopStrengthConeAction
open ConeTrack LoopStrength LoopConeTrack
variable {C : Type u} [Category.{v} C]

/-- Both original output loops of strength are evaluated without moving either coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthConeAction.lean:25-45"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem strength_cone_evaluation (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ) (t u : unitInterval)
    (x : (((strictDiagramFunctor Q).obj (F ⋙ parameterLoopingFunctor)).obj X).space n) :
    Path.toContinuousMap (Path.toContinuousMap ((strength Q F X).map n x) t) u =
      ((map Q (evaluationAt F t)).app X).map n (Path.toContinuousMap x u) := by
  exact congrArg (fun z => Path.toContinuousMap z u)
    (bassHomotopy_apply (E := F ⋙ parameterLoopingFunctor) (F := F)
      (evaluation F) (evaluation_naturality F) Q X n t x)

variable (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    (F : C ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
    (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
      (F.map (L.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- Strength intertwines the complete induced action, including the inverse index map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStrengthConeAction.lean:46-70"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem strength_action (X : C) (r : unitInterval) :
    strength Q F X ≫ parameterLoopingMap (parameterLoopingMap
      ((action Q L c χ hχ F H hH X).at r)) =
    parameterLoopingMap
      ((action Q L c χ hχ (F ⋙ parameterLoopingFunctor)
        (fun Y => (H Y).parameterLooping) (loop_naturality L c F H hH) X).at r) ≫
      strength Q F (L.obj X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext t
  apply Path.ext
  funext u
  let a := (action Q L c χ hχ F H hH X).at r
  let b := (action Q L c χ hχ (F ⋙ parameterLoopingFunctor)
    (fun Y => (H Y).parameterLooping) (loop_naturality L c F H hH) X).at r
  have h₁ := strength_cone_evaluation Q F X n t u x
  have h₂ := strength_cone_evaluation Q F (L.obj X) n t u
    ((parameterLoopingMap b).map n x)
  have h₃ := congrArg (fun k => k.map n (Path.toContinuousMap x u))
    (action_evaluation Q L c χ hχ F H hH X r t)
  exact (congrArg (fun z => a.map n z) h₁).trans (h₃.trans h₂.symm)

end KTheory.Bass.LoopStrengthConeAction
