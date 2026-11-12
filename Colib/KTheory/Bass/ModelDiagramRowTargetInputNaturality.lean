/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowReplacementStable
public import Colib.KTheory.Bass.ModelDiagramRowUnitTriangle
public import Colib.KTheory.Bass.ModelDiagramRowInputNaturality
public import Colib.Topology.Prespectrum.SuspensionLoopCounitNaturality

/-!
# Proper row replacement under exact Model transformations

The whole proper target replacement is natural for the original exact Model
maps, including supported-to-ambient and restriction maps. This statement
retains the computed row comparison and actual suspension evaluation counit.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u v w
namespace KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) {F G : C ⥤ WideSubcategory preservesZero.{w}} (η : F ⟶ G)

/-- Original coefficient arrows act on the whole proper row target. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:37"
  "adaptation" "Actual original proper-row target diagram."]
def targetDiagram (F : C ⥤ WideSubcategory preservesZero.{w}) : C ⥤ LoopPrespectrum.{w} :=
  ModelDiagramRowRefinement.diagram Q i F ⋙ parameterLoopingFunctor

/-- The actual input map on whole proper target diagrams. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowTargetInputNaturality.lean:27"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def inputNatTrans : targetDiagram Q i F ⟶ targetDiagram Q i G :=
  Functor.whiskerRight (ModelDiagramRowRefinement.inputNatTrans Q i η)
    parameterLoopingFunctor

/-- The original replacement counits and computed row maps preserve the input transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowTargetInputNaturality.lean:32"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem refinement_input_naturality (X : C) :
    parameterLoopingMap (suspensionConeMap (parameterLoopingMap
      ((ModelDiagramRowRefinement.inputSourceMap Q i η).app X))) ≫ refinement Q i G X =
    refinement Q i F X ≫ (inputNatTrans Q i η).app X := by
  let g : cone Q i F X ⟶ cone Q i G X :=
    (ModelDiagramRowRefinement.inputSourceMap Q i η).app X
  have hρ : g ≫ ModelDiagramRowRefinement.comparison Q i G X =
      ModelDiagramRowRefinement.comparison Q i F X ≫
        ModelDiagramRowRefinement.inputMap Q i η X :=
    ModelDiagramRowRefinement.comparison_input_naturality Q i η X
  change parameterLoopingFunctor.map (suspensionConeMap (parameterLoopingMap g)) ≫
      parameterLoopingFunctor.map (suspensionLoopCounit (cone Q i G X) ≫
        ModelDiagramRowRefinement.comparison Q i G X) =
    parameterLoopingFunctor.map (suspensionLoopCounit (cone Q i F X) ≫
      ModelDiagramRowRefinement.comparison Q i F X) ≫
        parameterLoopingFunctor.map (ModelDiagramRowRefinement.inputMap Q i η X)
  rw [← parameterLoopingFunctor.map_comp, ← parameterLoopingFunctor.map_comp]
  apply congrArg parameterLoopingFunctor.map
  rw [← Category.assoc, suspensionLoopCounit_naturality, Category.assoc, hρ,
    Category.assoc]

end KTheory.Bass.ModelDiagramRowStabilizedTarget
