/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.IteratedLoopStrength
public import Colib.KTheory.Bass.FiniteConeTopology
public import Colib.KTheory.Bass.StageAction
public import Colib.Topology.Prespectrum.LoopTranspose


/-!
# Actual finite stage maps into loop-normalized cone iterates

The map from the original finite Bass stage to `Omega^i C^i F` is formed from the original
Bass image of the preceding map and the fixed-order iterated loop strength. Both full functor
identifications are retained as explicit equality transports. The original stability theorem
for genuine Model input is deferred. These are stage maps only: no compatibility with
successive seed
transitions, no equality of geometric chi with cone-loop strength, and no tower comparison
is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.NormalizedStageMap
open FiniteConeTopology IteratedLoopStrength
variable {C : Type u} [Category.{v} C]

/-- The finite normalized object uses the same unlooped cone as the original cone action. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageMap.lean:33"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalized (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    C ⥤ LoopPrespectrum.{w} := loopDiagram i (iterate Q i F)

/-- Every normalized value is the literal finite cone followed by the original parameter loops. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageMap.lean:37"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem normalized_obj (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    (normalized Q i F).obj X = loops i ((iterate Q i F).obj X) :=
  loopDiagram_obj i _ X

/-- The original Bass functor is the same unlooped cone followed by parameter looping. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageMap.lean:52"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem bass_eq_loop_cone (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).obj F = ConeTrack.diagram Q F ⋙
      parameterLoopingFunctor := rfl

/-- The target of the prescribed iterated strength is the next normalized stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageMap.lean:57"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem normalized_succ_eq (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    loopDiagram i ((strictDiagramFunctor Q).obj (iterate Q i F)) =
      normalized Q (i + 1) F := by
  rw [bass_eq_loop_cone]
  exact loopDiagram_postcomp i (ConeTrack.diagram Q (iterate Q i F))

/-- Actual stage maps, retaining both complete source and target equality transports. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageMap.lean:65"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def stageMap (Q : C ⥤ Arrow (Arrow C)) :
    ∀ (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}),
      (strictDiagramIterate Q i).obj F ⟶ normalized Q i F
  | 0, F => 𝟙 F
  | i + 1, F => eqToHom (bass_succ_eq Q i F) ≫
      (strictDiagramFunctor Q).map (stageMap Q i F) ≫
      iteratedStrength Q i (iterate Q i F) ≫ eqToHom (normalized_succ_eq Q i F)


end KTheory.Bass.NormalizedStageMap
