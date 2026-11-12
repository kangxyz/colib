/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.FiniteFiberStructure
public import Colib.Topology.HomotopyFiber.FiniteSourceDetection

/-! # Finite source-structure detection through the original fiber

The fiber-loop transpose identifies the actual ladder map. The positive five lemma
then detects the source structure in the specified degree, with no stable premise.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/FiniteFiberSourceStructure.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The original target and fiber structures detect the source in degree k+2. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/FiniteFiberSourceStructure.lean:27"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem structure_source_bijective_of_fiber (n k : ℕ)
    (hThi : Function.Bijective (HomotopyGroup.map (N := Fin (k + 3))
      (F.structureMap n) (F.map_point n)))
    (hTlo : Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      (F.structureMap n) (F.map_point n)))
    (hFhi : Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      ((homotopyFiber f).structureMap n) ((homotopyFiber f).map_point n)))
    (hFlo : Function.Bijective (HomotopyGroup.map (N := Fin (k + 1))
      ((homotopyFiber f).structureMap n) ((homotopyFiber f).map_point n))) :
    Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      (E.structureMap n) (E.map_point n)) := by
  exact HomotopyFiber.piMap_source_bijective_of_basedFiberMap
    (E.structureMap n) (F.structureMap n)
    (by ext x t; exact (congrArg (fun p ↦ p t) (f.comm n x)).symm)
    (E.point n) (F.point n) (f.map_point n)
    (Path.refl (E.point (n + 1))) (Path.refl (F.point (n + 1)))
    (basedLoopMap_refl _ _) (E.map_point n) (F.map_point n) k hThi.surjective
    (homotopyFiberStructureComparison_bijective f n (k + 2) hFhi) hTlo
    (homotopyFiberStructureComparison_bijective f n (k + 1) hFlo).injective

end Topology.LoopPrespectrum
