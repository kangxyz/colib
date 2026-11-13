/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.ModelRowZigzagBackward
public import Colib.KTheory.Bass.ModelDiagramRowReplacementStable

/-! # Stability of the original proper-row backward leg

The original finite-range proof applies to the unchanged native construction.
-/
/-! Implementation provenance:
`Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelRowZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)

/-- Actual unit and row-refinement stability prove stability of the original backward leg. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean:40"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem backward_stable (n : ℕ) : IsStableEquivalence (backward Q M X n) :=
  (ModelDiagramSuspension.unit_stable Q n M X).comp
    (ModelDiagramRowStabilizedTarget.currentRefinement_stable Q n M X)

end KTheory.Bass.ModelRowZigzagSequentialization
