/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Topology.Prespectrum.FiniteLoopWordSlide

/-! # The innermost-transpose recursion of the fixed cyclic loop word -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open scoped Topology unitInterval
universe u v w
namespace Topology.LoopPrespectrum.FiniteLoopInnerRotation
open FiniteParameterLooping FiniteLoopWords
open FiniteLoopWordSlide
variable {C : Type u} [Category.{v} C]

/-- The full association cast appends precisely the original innermost evaluation time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopInnerRotation.lean:25"
  "adaptation" "Original finite seed rotation with full casts and fixed order."]
theorem postcomp_evaluate (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : ((loopDiagram i (F ⋙ parameterLoopingFunctor)).obj X).space n)
    (t : Fin (i + 1) → unitInterval) :
    evaluate (i + 1) F X n
        (((eqToHom (loopDiagram_postcomp i F)).app X).map n z) t =
      Path.toContinuousMap (evaluate i (F ⋙ parameterLoopingFunctor) X n z (Fin.init t))
        (t (Fin.last i)) := by
  have h : loopInto i (𝟙 (F ⋙ parameterLoopingFunctor)) =
      eqToHom (loopDiagram_postcomp i F) := by
    rw [loopInto_eq, loopMap_id, Category.id_comp]
  rw [← h]
  exact loopInto_evaluate i (𝟙 (F ⋙ parameterLoopingFunctor)) X n z t

/-- The exact inverse transpose is the same original coordinate swap. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopInnerRotation.lean:39"
  "adaptation" "Original finite seed rotation with full casts and fixed order."]
theorem transposeIso_inv (F : C ⥤ LoopPrespectrum.{w}) :
    (transposeIso F).inv = (transposeIso F).hom := rfl

/-- The old cyclic word preceded by the innermost inverse transpose is the next cyclic word.
All three complete association transports are displayed in the equation. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopInnerRotation.lean:44"
  "adaptation" "Original finite seed rotation with full casts and fixed order."]
theorem cyclicIso_succ_inner (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    loopMap i (transposeIso F).inv ≫
        eqToHom (loopDiagram_postcomp i (F ⋙ parameterLoopingFunctor)) ≫
        (cyclicIso i (F ⋙ parameterLoopingFunctor)).hom ≫
        eqToHom (loopDiagram_postcomp (i + 1) F) =
      eqToHom (loopDiagram_postcomp i (F ⋙ parameterLoopingFunctor)) ≫
        eqToHom (loopDiagram_postcomp (i + 1) F) ≫ (cyclicIso (i + 1) F).hom := by
  apply evaluation_hom_ext (i + 2)
  intro X n z t
  change evaluate (i + 2) F X n
      (((eqToHom (loopDiagram_postcomp (i + 1) F)).app X).map n
        (((cyclicIso i (F ⋙ parameterLoopingFunctor)).hom.app X).map n
          (((eqToHom (loopDiagram_postcomp i (F ⋙ parameterLoopingFunctor))).app X).map n
            (((loopMap i (transposeIso F).inv).app X).map n z)))) t =
    evaluate (i + 2) F X n (((cyclicIso (i + 1) F).hom.app X).map n
      (((eqToHom (loopDiagram_postcomp (i + 1) F)).app X).map n
        (((eqToHom (loopDiagram_postcomp i (F ⋙ parameterLoopingFunctor))).app X).map n z))) t
  erw [postcomp_evaluate, cyclicIso_evaluate, postcomp_evaluate, evaluate_loopMap,
    cyclicIso_evaluate, postcomp_evaluate, postcomp_evaluate]
  simp only [Fin.init_snoc, Fin.snoc_last]
  rfl

end Topology.LoopPrespectrum.FiniteLoopInnerRotation
