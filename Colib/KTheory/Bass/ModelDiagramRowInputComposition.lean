/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowTargetInputNaturality
public import Colib.Topology.Prespectrum.RowRefinementFunctoriality

/-! # Composition of the actual Model-input maps on proper row targets -/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology
universe u v w
private theorem row_map_comp_of_eq {E F G : Topology.LoopPrespectrum.{w}}
    (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
    (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
    (qG : ∀ k, C(G.space (k + 3), G.space (k + 3)))
    (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
    (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
    (hG : ∀ k, qG k (G.point (k + 3)) = G.point (k + 3))
    (a : E ⟶ F) (b : F ⟶ G) (c : E ⟶ G)
    (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))
    (hb : ∀ k x, qG k (b.map (k + 3) x) = b.map (k + 3) (qF k x))
    (hc : ∀ k x, qG k (c.map (k + 3) x) = c.map (k + 3) (qE k x))
    (h : c = a ≫ b) :
    RowRefinement.map qE qG hE hG c hc =
      RowRefinement.map qE qF hE hF a ha ≫ RowRefinement.map qF qG hF hG b hb := by
  subst c
  exact RowRefinement.map_comp _ _ _ _ _ _ _ _ _ _ _

namespace KTheory.Bass.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
  {F G H : C ⥤ WideSubcategory preservesZero.{w}} (η : F ⟶ G) (θ : G ⟶ H)

/-- Original cone input transformations preserve actual Model composition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInputComposition.lean:41"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inputSourceMap_comp :
    inputSourceMap Q i (η ≫ θ) = inputSourceMap Q i η ≫ inputSourceMap Q i θ := by
  simp only [inputSourceMap, ConeTrack.map, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Functor.map_comp]

/-- The proper row carrier map preserves those same original composite inputs. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInputComposition.lean:47"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inputMap_comp (X : C) :
    inputMap Q i (η ≫ θ) X = inputMap Q i η X ≫ inputMap Q i θ X := by
  exact row_map_comp_of_eq
    (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone Q i G X)
    (ModelDiagramRowInterchange.cone Q i H X)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i G X)
    (ModelDiagramRowInterchange.cone_point Q i H X)
    ((inputSourceMap Q i η).app X) ((inputSourceMap Q i θ).app X)
    ((inputSourceMap Q i (η ≫ θ)).app X)
    (ModelDiagramRowInterchange.cone_input_naturality Q η i X)
    (ModelDiagramRowInterchange.cone_input_naturality Q θ i X)
    (ModelDiagramRowInterchange.cone_input_naturality Q (η ≫ θ) i X)
    (congrArg (fun a => a.app X) (inputSourceMap_comp Q i η θ))

end KTheory.Bass.ModelDiagramRowRefinement

namespace KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
  {F G H : C ⥤ WideSubcategory preservesZero.{w}} (η : F ⟶ G) (θ : G ⟶ H)

/-- Parameter looping preserves actual composition of the complete proper-row input maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInputComposition.lean:70"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inputNatTrans_comp :
    inputNatTrans Q i (η ≫ θ) = inputNatTrans Q i η ≫ inputNatTrans Q i θ := by
  ext X
  change parameterLoopingFunctor.map (ModelDiagramRowRefinement.inputMap Q i (η ≫ θ) X) =
    parameterLoopingFunctor.map (ModelDiagramRowRefinement.inputMap Q i η X) ≫
      parameterLoopingFunctor.map (ModelDiagramRowRefinement.inputMap Q i θ X)
  rw [ModelDiagramRowRefinement.inputMap_comp, Functor.map_comp]

end KTheory.Bass.ModelDiagramRowStabilizedTarget
