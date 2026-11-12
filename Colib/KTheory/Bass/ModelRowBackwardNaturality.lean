/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelRowZigzagBackward
public import Colib.KTheory.Bass.ModelRowZigzagBackwardStable
public import Colib.KTheory.Bass.NormalizedStageMap
public import Colib.KTheory.Bass.StageAction
public import Colib.KTheory.Bass.NormalizedStageMapStable
public import Colib.KTheory.Bass.ModelDiagramRowTargetInputNaturality

/-!
# Naturality of the original proper-row backward legs

The full original successor identification and parameter-looped row comparison
assemble the already constructed backward legs into a natural transformation.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u v w
namespace KTheory.Bass.ModelRowZigzagSequentialization
open NormalizedStageMap
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (M : C ⥤ WideSubcategory preservesZero.{w}) (i : ℕ)

/-- The entire original successor diagram is the looped original cone diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelRowBackwardNaturality.lean:28"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem successor_diagram :
    (strictDiagramIterate Q (i + 1)).obj (M ⋙ prespectrumFunctor) =
      ModelDiagramRowRefinement.sourceDiagram Q i M ⋙ parameterLoopingFunctor :=
  (bass_succ_eq Q i (M ⋙ prespectrumFunctor)).trans
    (bass_eq_loop_cone Q ((strictDiagramIterate Q i).obj (M ⋙ prespectrumFunctor)))

/-- The same original backward legs assemble without choosing any new maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelRowBackwardNaturality.lean:35"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def backwardNatTrans :
    (strictDiagramIterate Q (i + 1)).obj (M ⋙ prespectrumFunctor) ⟶
      ModelDiagramRowStabilizedTarget.targetDiagram Q i M :=
  eqToHom (successor_diagram Q M i) ≫
    ModelDiagramRowRefinement.parameterComparisonNatTrans Q i M

/-- Every component is the already constructed original unit followed by target replacement. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelRowBackwardNaturality.lean:42"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem backwardNatTrans_app (X : C) :
    (backwardNatTrans Q M i).app X = backward Q M X i := by
  rw [backward_eq]
  change (eqToHom (successor_diagram Q M i)).app X ≫
    parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i M X) = _
  rw [eqToHom_app]
  rfl

/-- Original coefficient arrows commute with the whole backward maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelRowBackwardNaturality.lean:51"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem backward_naturality {X Y : C} (f : X ⟶ Y) :
    ((strictDiagramIterate Q (i + 1)).obj (M ⋙ prespectrumFunctor)).map f ≫
        backward Q M Y i =
      backward Q M X i ≫ (ModelDiagramRowStabilizedTarget.targetDiagram Q i M).map f := by
  simpa only [backwardNatTrans_app, target, ModelDiagramRowStabilizedTarget.target,
    ModelDiagramRowStabilizedTarget.targetDiagram, Functor.comp_obj,
    ModelDiagramRowRefinement.diagram, parameterLoopingFunctor] using
    (backwardNatTrans Q M i).naturality f

section Input
variable {M' : C ⥤ WideSubcategory preservesZero.{w}} (η : M ⟶ M')

/-- The actual original successor casts preserve the exact input Model map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelRowBackwardNaturality.lean:64"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem successor_input_square (X : C) :
    (((strictDiagramIterate Q (i + 1)).map
      (Functor.whiskerRight η prespectrumFunctor)).app X) ≫
        eqToHom (ModelDiagramSuspension.successor_obj Q i M' X) =
    eqToHom (ModelDiagramSuspension.successor_obj Q i M X) ≫
      parameterLoopingMap ((ModelDiagramRowRefinement.inputSourceMap Q i η).app X) := by
  have h := (eqToHom (strictDiagramIterate_succ_right Q i)).naturality
    (Functor.whiskerRight η prespectrumFunctor)
  have hx := congrArg (fun t => t.app X) h
  simp only [NatTrans.comp_app, eqToHom_app, Functor.comp_map] at hx
  exact hx

/-- The backward leg retains the whole original exact input square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelRowBackwardNaturality.lean:77"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem backward_input_naturality (X : C) :
    (((strictDiagramIterate Q (i + 1)).map
      (Functor.whiskerRight η prespectrumFunctor)).app X) ≫ backward Q M' X i =
    backward Q M X i ≫ (ModelDiagramRowStabilizedTarget.inputNatTrans Q i η).app X := by
  rw [backward_eq, backward_eq]
  change (((strictDiagramIterate Q (i + 1)).map
      (Functor.whiskerRight η prespectrumFunctor)).app X) ≫
      (eqToHom (ModelDiagramSuspension.successor_obj Q i M' X) ≫
        parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i M' X)) =
    (eqToHom (ModelDiagramSuspension.successor_obj Q i M X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i M X)) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.inputMap Q i η X)
  rw [← Category.assoc, successor_input_square, Category.assoc, Category.assoc]
  have hr := congrArg parameterLoopingFunctor.map
    (ModelDiagramRowRefinement.comparison_input_naturality Q i η X)
  rw [Functor.map_comp, Functor.map_comp] at hr
  exact congrArg (fun k => eqToHom (ModelDiagramSuspension.successor_obj Q i M X) ≫ k) hr

end Input

end KTheory.Bass.ModelRowZigzagSequentialization
