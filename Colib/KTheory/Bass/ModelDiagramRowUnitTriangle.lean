/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SuspensionLoopUnit
public import Colib.KTheory.Bass.ModelDiagramSuccessor
public import Colib.KTheory.Bass.ModelDiagramRowComparison

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
namespace KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The same original unlooped cone, with its actual finite-stage model input. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:30"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
abbrev cone (X : C) : LoopPrespectrum.{w} := ModelDiagramRowRefinement.source Q i F X

/-- The actual target has the computed row-compatible structure maps. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:33"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def target (X : C) : LoopPrespectrum.{w} :=
  parameterLooping (ModelDiagramRowRefinement.carrier Q i F X)

/-- The actual counit followed by the original row comparison gives replacement. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:41"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def refinement (X : C) :
    parameterLooping (suspensionCone (parameterLooping (cone Q i F X))) ⟶ target Q i F X :=
  parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
    ModelDiagramRowRefinement.comparison Q i F X)

/-- The original suspension unit followed by replacement is exactly the looped row comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:53"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
theorem unit_refinement (X : C) :
    suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫ refinement Q i F X =
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) := by
  change suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫
    parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
      ModelDiagramRowRefinement.comparison Q i F X) = _
  rw [show parameterLoopingMap (suspensionLoopCounit (cone Q i F X) ≫
      ModelDiagramRowRefinement.comparison Q i F X) =
    parameterLoopingMap (suspensionLoopCounit (cone Q i F X)) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) from
        parameterLoopingFunctor.map_comp _ _]
  rw [← Category.assoc, suspensionLoopUnit_counit, Category.id_comp]

/-- Literal original successor objects retain their existing whole-spectrum identification. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:67"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def currentRefinement (X : C) :
    parameterLooping (suspensionCone
      (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X)) ⟶
        target Q i F X :=
  eqToHom (congrArg (fun E => parameterLooping (suspensionCone E))
    (ModelDiagramSuspension.successor_obj Q i F X)) ≫ refinement Q i F X

@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:145"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
private theorem unit_transport {E G : LoopPrespectrum.{w}} (h : E = G) :
    suspensionLoopUnit E ≫
        eqToHom (congrArg (fun A => parameterLooping (suspensionCone A)) h) =
      eqToHom h ≫ suspensionLoopUnit G := by
  subst G
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The literal original successor unit retains its actual spectrum transport in the triangle. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:153"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
theorem current_unit_refinement (X : C) :
    suspensionLoopUnit
        (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X) ≫
      currentRefinement Q i F X =
    eqToHom (ModelDiagramSuspension.successor_obj Q i F X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) := by
  unfold currentRefinement
  rw [← Category.assoc, unit_transport (ModelDiagramSuspension.successor_obj Q i F X),
    Category.assoc, unit_refinement]

end KTheory.Bass.ModelDiagramRowStabilizedTarget

attribute [colib_tag "COL-0553"]
  KTheory.Bass.ModelDiagramRowStabilizedTarget.current_unit_refinement
