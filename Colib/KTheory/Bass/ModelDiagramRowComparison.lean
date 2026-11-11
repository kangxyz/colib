/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowInterchange
public import Colib.Topology.Prespectrum.RowRefinement

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
namespace KTheory.Bass.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The unchanged original comparison cone at the specified finite Bass stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean:32"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
abbrev source (X : C) : LoopPrespectrum.{w} :=
  (ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X

/-- The genuine distinguished-row target uses the computed original finite-stage interchange. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean:36"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def carrier (X : C) : LoopPrespectrum.{w} :=
  RowRefinement.spectrum (source Q i F X) (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i F X)

/-- The actual original structure maps give the complete finite-stage comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean:41"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def comparison (X : C) : source Q i F X ⟶ carrier Q i F X :=
  RowRefinement.comparison (source Q i F X) (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    (ModelDiagramRowInterchange.cone_structure Q i F X)

end KTheory.Bass.ModelDiagramRowRefinement
