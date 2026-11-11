/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.IteratedStrengthNaturality
public import Colib.KTheory.Bass.NormalizedStageMap

/-! # The alternate successor of the fixed Bass strength, retaining full casts -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.IteratedStrengthSuccessor
open FiniteConeStrength IteratedLoopStrength
open FiniteLoopWords NormalizedStageMap IteratedStrengthNaturality
variable {C : Type u} [Category.{v} C]

/-- Whiskering an equality-induced diagram map retains the induced equality. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedStrengthSuccessor.lean:25"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem whiskerRight_eqToHom {F G : C ⥤ LoopPrespectrum.{w}} (h : F = G) :
    Functor.whiskerRight (eqToHom h) parameterLoopingFunctor =
      eqToHom (congrArg (fun H => H ⋙ parameterLoopingFunctor) h) := by
  subst G
  exact Functor.whiskerRight_id' parameterLoopingFunctor

/-- The prescribed full association equality is looped at each successor. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedStrengthSuccessor.lean:32"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem loopDiagram_postcomp_succ (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    eqToHom (loopDiagram_postcomp (i + 1) F) =
      Functor.whiskerRight (eqToHom (loopDiagram_postcomp i F)) parameterLoopingFunctor := by
  rw [whiskerRight_eqToHom]

/-- Moving the innermost crossing to the end preserves the actual fixed strength. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedStrengthSuccessor.lean:38"
  "adaptation" "Original strength evaluation, naturality and full casts."]
theorem iteratedStrength_succ_inner (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).map (eqToHom (loopDiagram_postcomp i F)) ≫
        iteratedStrength Q (i + 1) F =
      iteratedStrength Q i (F ⋙ parameterLoopingFunctor) ≫
        loopMap i (strengthDiagram Q F) ≫
          eqToHom (loopDiagram_postcomp i ((strictDiagramFunctor Q).obj F)) := by
  induction i with
  | zero =>
    change (strictDiagramFunctor Q).map (𝟙 _) ≫
        (strengthDiagram Q F ≫ Functor.whiskerRight (𝟙 _) parameterLoopingFunctor) =
      𝟙 _ ≫ strengthDiagram Q F ≫ 𝟙 _
    rw [(strictDiagramFunctor Q).map_id]
    simp only [Functor.whiskerRight_id', Category.comp_id, Category.id_comp]
  | succ i ih =>
    rw [loopDiagram_postcomp_succ]
    change _ ≫ (strengthDiagram Q (loopDiagram (i + 1) F) ≫
      Functor.whiskerRight (iteratedStrength Q (i + 1) F) parameterLoopingFunctor) =
      (strengthDiagram Q (loopDiagram i (F ⋙ parameterLoopingFunctor)) ≫
        Functor.whiskerRight (iteratedStrength Q i (F ⋙ parameterLoopingFunctor))
          parameterLoopingFunctor) ≫
        Functor.whiskerRight (loopMap i (strengthDiagram Q F)) parameterLoopingFunctor ≫ _
    rw [← Category.assoc, strengthDiagram_naturality, Category.assoc,
      ← Functor.whiskerRight_comp, ih, Functor.whiskerRight_comp,
      Functor.whiskerRight_comp, loopDiagram_postcomp_succ]
    simp only [Category.assoc]

end KTheory.Bass.IteratedStrengthSuccessor
