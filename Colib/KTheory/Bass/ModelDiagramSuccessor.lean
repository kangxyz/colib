/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowInterchange
public import Colib.KTheory.Bass.StrictDiagramSuccessor

/-! # The original actual successor, counit and backward triangle

Only the selected original construction and exact triangle are migrated here.
No stability, connectivity or telescope comparison is assumed or claimed.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.ModelDiagramSuspension
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The whole original successor object is the parameter loop of its previous square cone. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:51"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
theorem successor_obj (X : C) :
    ((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X =
      parameterLooping ((ConeTrack.diagram Q
        ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X) := by
  rw [strictDiagramIterate_succ_right]
  rfl

end KTheory.Bass.ModelDiagramSuspension
