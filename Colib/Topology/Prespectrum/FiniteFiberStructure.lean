/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.HomotopyFiber.FiniteTargetDetection
public import Colib.Topology.Prespectrum.FiberOmega

/-!
# The finite structure ladder of an actual prespectrum fiber

The original fiber structure is the actual structure-square map followed by the
explicit fiber-loop homeomorphism. Its two neighboring chosen-point bijections,
with those of the source structure, detect the target structure in degree k+2.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/FiniteFiberStructure.lean` at Quillen commit
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

/-- The actual structure square fixes the explicitly specified loop-fiber point. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/FiniteFiberStructure.lean:29"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem homotopyFiberStructureComparison_point (n : ℕ) :
    homotopyFiberStructureComparison f n ((homotopyFiber f).point n) =
      HomotopyFiber.basepoint (basedLoopMap (f.map (n + 1)) (f.map_point (n + 1)))
        (Path.refl (F.point (n + 1))) (Path.refl (E.point (n + 1)))
        (basedLoopMap_refl _ _) :=
  HomotopyFiber.mapAt_basepoint _ _ _ _ _ _ _ (f.map_point n)
    (basedLoopMap_refl _ _) (E.map_point n) (F.map_point n)

/-- Removing only the genuine fiber-loop homeomorphism retains a finite bijection. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/FiniteFiberStructure.lean:38"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem homotopyFiberStructureComparison_bijective (n k : ℕ)
    (hf : Function.Bijective (HomotopyGroup.map (N := Fin k)
      ((homotopyFiber f).structureMap n) ((homotopyFiber f).map_point n))) :
    Function.Bijective (HomotopyGroup.map (N := Fin k)
      (homotopyFiberStructureComparison f n) (homotopyFiberStructureComparison_point f n)) := by
  let e := HomotopyFiber.loopFiberHomeomorph (f.map (n + 1)) (f.map_point (n + 1))
  have hp := HomotopyFiber.loopFiberHomeomorph_basepoint (f.map (n + 1)) (f.map_point (n + 1))
  have he := homotopyGroupMap_bijective_of_homotopyEquiv e.toHomotopyEquiv hp k
  have hw : HomotopyGroup.map (N := Fin k) e.toHomotopyEquiv.toFun hp ∘
      HomotopyGroup.map (N := Fin k) (homotopyFiberStructureComparison f n)
        (homotopyFiberStructureComparison_point f n) =
      HomotopyGroup.map (N := Fin k) ((homotopyFiber f).structureMap n)
        ((homotopyFiber f).map_point n) := by
    funext z
    simp only [Function.comp_apply]
    erw [← HomotopyGroup.map_comp]
    congr 1
  rw [← hw] at hf
  exact (Function.Bijective.of_comp_iff' he _).mp hf

/-- Two exact neighboring source and fiber degrees detect the original target structure. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/FiniteFiberStructure.lean:59"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem structure_target_bijective_of_fiber (n k : ℕ)
    (hEhi : Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      (E.structureMap n) (E.map_point n)))
    (hElo : Function.Bijective (HomotopyGroup.map (N := Fin (k + 1))
      (E.structureMap n) (E.map_point n)))
    (hFhi : Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      ((homotopyFiber f).structureMap n) ((homotopyFiber f).map_point n)))
    (hFlo : Function.Bijective (HomotopyGroup.map (N := Fin (k + 1))
      ((homotopyFiber f).structureMap n) ((homotopyFiber f).map_point n))) :
    Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      (F.structureMap n) (F.map_point n)) := by
  exact HomotopyFiber.piMap_target_bijective_of_basedFiberMap
    (E.structureMap n) (F.structureMap n)
    (by ext x t; exact (congrArg (fun p ↦ p t) (f.comm n x)).symm)
    (E.point n) (F.point n) (f.map_point n)
    (Path.refl (E.point (n + 1))) (Path.refl (F.point (n + 1)))
    (basedLoopMap_refl _ _) (E.map_point n) (F.map_point n) k
    (homotopyFiberStructureComparison_bijective f n (k + 2) hFhi).surjective
    hEhi (homotopyFiberStructureComparison_bijective f n (k + 1) hFlo) hElo.injective

end Topology.LoopPrespectrum
