/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.PushoutConeFiniteRange
public import Colib.KTheory.Bass.StrictDiagram

/-!
# One-step finite structure range of the actual Bass endofunctor

The input consists of actual chosen-point structure bijections, original point HEP,
and all-point growth. No Omega condition is imposed on a later Bass stage.
-/
/-! Implementation provenance:
`Quillen/KTheory/Bass/StrictDiagramFiniteStructure.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
universe u v w
namespace KTheory.Bass
open Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- One original Bass step preserves slope two and raises the level offset by one. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramFiniteStructure.lean:26"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem strictDiagramFunctor_structure_bijective (F : C ⥤ LoopPrespectrum.{w}) (c : ℕ)
    (h : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (hπ : ∀ X n x j, j < n + 2 →
      Subsingleton (HomotopyGroup.Pi j ((F.obj X).space (n + c + 2)) x))
    (hσ : ∀ X n j, 0 < j → j < 2 * n + 2 →
      Function.Bijective (HomotopyGroup.map (N := Fin j)
        ((F.obj X).structureMap (n + c + 2)) ((F.obj X).map_point _)))
    (X : C) (n j : ℕ) (hj : 0 < j) (hr : j < 2 * n + 2) :
    Function.Bijective (HomotopyGroup.map (N := Fin j)
      ((((strictDiagramFunctor Q).obj F).obj X).structureMap (n + (c + 1) + 2))
      ((((strictDiagramFunctor Q).obj F).obj X).map_point _)) := by
  exact loopedPushoutCone_structure_bijective_of_finite_corners
    (F.map (Q.obj X).left.hom) (F.map (Q.obj X).hom.left)
    (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))) c
    (h _) (h _) (h _) (h _) (hπ _) (hπ _) (hπ _) (hπ _)
    (hσ _) (hσ _) (hσ _) (hσ _) n j hj hr

end KTheory.Bass
