/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowInputComposition

/-! # Identity input on the actual proper-row target -/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology
universe u v w

private theorem row_map_id_of_eq {E : Topology.LoopPrespectrum.{w}}
    (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
    (hp : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
    (a : E ⟶ E)
    (ha : ∀ k x, q k (a.map (k + 3) x) = a.map (k + 3) (q k x))
    (h : a = 𝟙 E) : RowRefinement.map q q hp hp a ha = 𝟙 _ := by
  subst a
  exact RowRefinement.map_id q hp ha

namespace KTheory.Bass.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
  (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The original identity Model transformation acts identically on the unlooped cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInputIdentity.lean:33"
  "adaptation" "Original input maps preserve composition, identities and whole null squares."]
theorem inputSourceMap_id : inputSourceMap Q i (𝟙 F) = 𝟙 _ := by
  simp only [inputSourceMap, ConeTrack.map, Functor.whiskerRight_id',
    CategoryTheory.Functor.map_id]
  rfl

/-- The computed proper-row input of an original identity is the actual identity. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInputIdentity.lean:39"
  "adaptation" "Original input maps preserve composition, identities and whole null squares."]
theorem inputMap_id (X : C) : inputMap Q i (𝟙 F) X = 𝟙 _ :=
  row_map_id_of_eq
    (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    ((inputSourceMap Q i (𝟙 F)).app X)
    (ModelDiagramRowInterchange.cone_input_naturality Q (𝟙 F) i X)
    (congrArg (fun a => a.app X) (inputSourceMap_id Q i F))

end KTheory.Bass.ModelDiagramRowRefinement

namespace KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
  (F : C ⥤ WideSubcategory preservesZero.{w})

/-- Original identity inputs stay identities after parameter looping. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInputIdentity.lean:54"
  "adaptation" "Original input maps preserve composition, identities and whole null squares."]
theorem inputNatTrans_id : inputNatTrans Q i (𝟙 F) = 𝟙 _ := by
  ext X
  change parameterLoopingFunctor.map (ModelDiagramRowRefinement.inputMap Q i (𝟙 F) X) = 𝟙 _
  rw [ModelDiagramRowRefinement.inputMap_id, CategoryTheory.Functor.map_id]

end KTheory.Bass.ModelDiagramRowStabilizedTarget
