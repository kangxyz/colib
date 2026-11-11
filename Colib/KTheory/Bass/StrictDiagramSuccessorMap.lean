/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagramSuccessorTransition

/-!
# Natural successor maps for the original strict Bass iteration

The successor map is precisely the equality-induced map from the original right-iteration
identity. It is natural in every strict diagram arrow and intertwines the original transitions.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- The actual right-successor equality, evaluated on the original diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramSuccessorMap.lean:24"
  "adaptation" "Original successor transports and same-time iterated null."]
def strictDiagramSuccessorMap (F : C ⥤ LoopPrespectrum.{w}) (i : ℕ) :
    (strictDiagramIterate Q (i + 1)).obj F ⟶
      (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F) :=
  eqToHom (congrArg (fun H ↦ H.obj F) (strictDiagramIterate_succ_right Q i))

/-- The unchanged equality-induced successor arrow is an isomorphism. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramSuccessorMap.lean:30"
  "adaptation" "Original equality-induced successor isomorphism."]
instance strictDiagramSuccessorMap_isIso (F : C ⥤ LoopPrespectrum.{w}) (i : ℕ) :
    IsIso (strictDiagramSuccessorMap Q F i) := by
  unfold strictDiagramSuccessorMap
  infer_instance

/-- The specified successor transport is natural in every original diagram arrow. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramSuccessorMap.lean:36"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramSuccessorMap_naturality
    {F G : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (i : ℕ) :
    (strictDiagramIterate Q (i + 1)).map a ≫ strictDiagramSuccessorMap Q G i =
      strictDiagramSuccessorMap Q F i ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q i).map a) := by
  have h := (eqToHom (strictDiagramIterate_succ_right.{u, v, w} Q i)).naturality a
  simpa only [eqToHom_app, Functor.comp_map, strictDiagramSuccessorMap] using h

/-- The original successor transitions retain these exact equality-induced maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramSuccessorMap.lean:45"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramSuccessorMap_transition
    {F : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ (strictDiagramFunctor Q).obj F) (i : ℕ) :
    strictDiagramTransition Q η (i + 1) ≫ strictDiagramSuccessorMap Q F (i + 1) =
      strictDiagramSuccessorMap Q F i ≫
        (strictDiagramFunctor Q).map (strictDiagramTransition Q η i) :=
  strictDiagramTransition_succ_right Q η i

end KTheory.Bass
