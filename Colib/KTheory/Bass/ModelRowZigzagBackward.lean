/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowUnitTriangle
public import Colib.KTheory.Bass.ModelZigzagVertices

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
namespace KTheory.Bass.ModelRowZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)

/-- The unchanged original finite Bass vertices. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean:29"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
abbrev vertex := ModelZigzagSequentialization.vertex Q M X

/-- Each proper target is the parameter loop of the actual computed cone row refinement. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean:32"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
abbrev target (n : ℕ) := ModelDiagramRowStabilizedTarget.target Q n M X

/-- The literal unit followed by the original proper target replacement. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean:35"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def backward (n : ℕ) : vertex Q M X (n + 1) ⟶ target Q M X n :=
  ModelZigzagSequentialization.unit Q M X n ≫
    ModelDiagramRowStabilizedTarget.currentRefinement Q n M X

/-- Its exact triangle retains the original successor transport and computed row comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean:45"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
theorem backward_eq (n : ℕ) :
    backward Q M X n = eqToHom (ModelDiagramSuspension.successor_obj Q n M X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q n M X) :=
  ModelDiagramRowStabilizedTarget.current_unit_refinement Q n M X

end KTheory.Bass.ModelRowZigzagSequentialization

attribute [colib_tag "COL-0553"]
  KTheory.Bass.ModelRowZigzagSequentialization.backward

attribute [colib_tag "COL-0553"]
  KTheory.Bass.ModelRowZigzagSequentialization.backward_eq
