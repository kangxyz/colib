/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.ModelDiagramRowUnitTriangle
public import Colib.KTheory.Bass.ModelDiagramSuspension
public import Colib.KTheory.Bass.ModelDiagramRowStability

/-! # Stability of the actual proper-row replacement

The original finite-range proof applies to the unchanged native construction.
-/
/-! Implementation provenance:
`Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean` at Quillen commit
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
namespace KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The proper replacement is stable from the proved actual counit and finite row range. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:47"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem refinement_stable (X : C) : IsStableEquivalence (refinement Q i F X) :=
  parameterLoopingMap_isStableEquivalence _
    ((ModelDiagramSuspension.cone_counit_stable Q i F X).comp
      (ModelDiagramRowRefinement.comparison_isStableEquivalence Q i F X))

/-- Replacement at each original successor is stable without new model hypotheses. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:75"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem currentRefinement_stable (X : C) :
    IsStableEquivalence (currentRefinement Q i F X) := by
  apply IsStableEquivalence.comp _ (refinement_stable Q i F X)
  intro d
  infer_instance

end KTheory.Bass.ModelDiagramRowStabilizedTarget
