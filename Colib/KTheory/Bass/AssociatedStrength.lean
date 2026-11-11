/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.IteratedStrengthSuccessor

/-! # The original finite strength with its existing complete association cast -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.AssociatedStrength
open FiniteConeStrength IteratedLoopStrength
open FiniteLoopWords NormalizedStageMap IteratedStrengthNaturality
open IteratedStrengthSuccessor
variable {C : Type u} [Category.{v} C]

/-- The original Bass map is precisely the loop of its original unlooped cone map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/AssociatedStrength.lean:25"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem bass_map_loop_cone (Q : C ⥤ Arrow (Arrow C))
    {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G) :
    (strictDiagramFunctor Q).map f =
      Functor.whiskerRight (ConeTrack.map Q f) parameterLoopingFunctor := rfl

/-- The complete loop-association cast is natural in every diagram map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/AssociatedStrength.lean:31"
  "adaptation" "Original strength evaluation, naturality and full casts.", reassoc]
theorem postcomp_naturality (i : ℕ) {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G) :
    loopMap i (Functor.whiskerRight f parameterLoopingFunctor) ≫
        eqToHom (loopDiagram_postcomp i G) =
      eqToHom (loopDiagram_postcomp i F) ≫ loopMap (i + 1) f := by
  induction i with
  | zero =>
    change Functor.whiskerRight f parameterLoopingFunctor ≫ 𝟙 _ =
      𝟙 _ ≫ Functor.whiskerRight f parameterLoopingFunctor
    rw [Category.comp_id, Category.id_comp]
  | succ i ih =>
    change Functor.whiskerRight
      (loopMap i (Functor.whiskerRight f parameterLoopingFunctor)) parameterLoopingFunctor ≫ _ =
      _ ≫ Functor.whiskerRight (loopMap (i + 1) f) parameterLoopingFunctor
    rw [loopDiagram_postcomp_succ, loopDiagram_postcomp_succ,
      ← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, ih]

/-- This abbreviation retains the unchanged finite strength and its prescribed full cast. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/AssociatedStrength.lean:48"
  "adaptation" "Original strength evaluation, naturality and full casts."]
def associatedStrength (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).obj (loopDiagram i F) ⟶
      loopDiagram (i + 1) (ConeTrack.diagram Q F) :=
  iteratedStrength Q i F ≫
    eqToHom (loopDiagram_postcomp i (ConeTrack.diagram Q F))

/-- Its naturality uses the complete original cone map, without changing any casts. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/AssociatedStrength.lean:56"
  "adaptation" "Original strength evaluation, naturality and full casts.", reassoc]
theorem associatedStrength_naturality (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G) :
    (strictDiagramFunctor Q).map (loopMap i f) ≫ associatedStrength Q i G =
      associatedStrength Q i F ≫ loopMap (i + 1) (ConeTrack.map Q f) := by
  unfold associatedStrength
  rw [← Category.assoc, iteratedStrength_naturality, Category.assoc, bass_map_loop_cone,
    postcomp_naturality, ← Category.assoc]

/-- The already fixed stage map uses precisely this associated strength. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/AssociatedStrength.lean:65"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem stageMap_succ (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    stageMap Q (i + 1) F = eqToHom (bass_succ_eq Q i F) ≫
      (strictDiagramFunctor Q).map (stageMap Q i F) ≫
        associatedStrength Q i (FiniteConeTopology.iterate Q i F) := rfl

end KTheory.Bass.AssociatedStrength
