/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.ModelDiagramFiniteStructure

/-!
# Original unlooped cone ranges at all finite Bass stages

The actual four corners of every finite stage satisfy the finite ladder. This supplies the
chosen-point range used by a row refinement comparison once its genuine row action is given.
-/
/-! Implementation provenance:
`Quillen/KTheory/Bass/ModelDiagramConeFiniteStructure.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Every original finite-stage comparison cone has the stated linear structure range. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramConeFiniteStructure.lean:24"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem modelDiagramIterate_cone_structure_bijective (i : ℕ)
    (F : C ⥤ WideSubcategory preservesZero.{w})
    (X : C) (n k : ℕ) (hk : k + 2 < 2 * n + 2) :
    Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
          (Q.obj X)))).structureMap (n + i + 3))
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
          (Q.obj X)))).map_point _)) := by
  let G := (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)
  rw [show n + i + 3 = (n + 1) + i + 2 by omega]
  exact pushoutCone_structure_bijective_of_finite_corners
    (G.map (Q.obj X).left.hom) (G.map (Q.obj X).hom.left)
    (StrictSquare.comparison (G.mapArrow.mapArrow.obj (Q.obj X))) i
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F _)
    (fun m x j hj ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (fun m x j hj ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (fun m x j hj ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (fun m x j hj ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q i F _ m j hj x)
    (modelDiagramIterate_structure_bijective Q i F _)
    (modelDiagramIterate_structure_bijective Q i F _)
    (modelDiagramIterate_structure_bijective Q i F _)
    (modelDiagramIterate_structure_bijective Q i F _)
    (n + 1) (k + 2) (by omega) (by omega)

end KTheory.Bass
