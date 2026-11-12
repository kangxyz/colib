/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.FiniteFiberStructure
public import Colib.Topology.Prespectrum.FiniteStructureTransport
public import Colib.Topology.Prespectrum.ConeLinearExcision

/-!
# Finite structure ranges of the original mapping cone

The original source-to-fiber comparison and its structure square transport finite
bijections to the actual fiber. The original fiber ladder then proves the same
range for the cone structure. The range concerns chosen-point groups only.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/ConeFiniteStructure.lean` at Quillen commit
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
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (c : ℕ)
  (hE : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + c + 2)))))
  (hF : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + c + 2)))))
  (hπE : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (E.space (n + c + 2)) x))
  (hπF : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (F.space (n + c + 2)) x))

include hE hF hπE hπF

/-- Finite excision retains the literal chosen point of the cone fiber. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeFiniteStructure.lean:40"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem coneFiberComparison_bijective_of_linearGrowth (n j : ℕ) (hj : j < 2 * n + 2) :
    Function.Bijective (HomotopyGroup.map (N := Fin j)
      ((mappingConeFiberComparison f).map (n + c + 2))
      ((mappingConeFiberComparison f).map_point (n + c + 2))) := by
  have hc := mappingConeFiberComparison_isHomotopyConnectedMap_of_linearGrowth
    f c n (hE n) (hF n) (hπE n) (hπF n)
  have hb {y} (h : (mappingConeFiberComparison f).map (n + c + 2)
      (E.point (n + c + 2)) = y) :
      Function.Bijective (HomotopyGroup.map (N := Fin j)
        ((mappingConeFiberComparison f).map (n + c + 2)) h) := by
    cases h
    exact hc.homotopyGroupMap_bijective _ j hj
  exact hb _

/-- The actual cone-fiber structure inherits the source structure in the finite excision range. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeFiniteStructure.lean:55"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem coneFiber_structure_bijective (n j : ℕ) (hj : j < 2 * n + 2)
    (hs : Function.Bijective (HomotopyGroup.map (N := Fin j)
      (E.structureMap (n + c + 2)) (E.map_point (n + c + 2)))) :
    Function.Bijective (HomotopyGroup.map (N := Fin j)
      ((homotopyFiber (mappingConeInclusion f)).structureMap (n + c + 2))
      ((homotopyFiber (mappingConeInclusion f)).map_point (n + c + 2))) := by
  apply structure_bijective_of_map (mappingConeFiberComparison f) (n + c + 2) j
  · exact coneFiberComparison_bijective_of_linearGrowth f c hE hF hπE hπF n j hj
  · have hh := coneFiberComparison_bijective_of_linearGrowth f c hE hF hπE hπF
      (n + 1) (j + 1) (by omega)
    rw [show n + c + 2 + 1 = (n + 1) + c + 2 by omega]
    exact hh
  · exact hs

/-- Two neighboring original structure degrees imply the cone structure in degree k+2. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeFiniteStructure.lean:70"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem mappingCone_structure_bijective (n k r : ℕ) (hr : r ≤ 2 * n + 2) (hk : k + 2 < r)
    (hsE : ∀ j, 0 < j → j < r →
      Function.Bijective (HomotopyGroup.map (N := Fin j)
        (E.structureMap (n + c + 2)) (E.map_point (n + c + 2))))
    (hsF : ∀ j, 0 < j → j < r →
      Function.Bijective (HomotopyGroup.map (N := Fin j)
        (F.structureMap (n + c + 2)) (F.map_point (n + c + 2)))) :
    Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
      ((mappingCone f).structureMap (n + c + 2)) ((mappingCone f).map_point (n + c + 2))) := by
  apply structure_target_bijective_of_fiber (mappingConeInclusion f) (n + c + 2) k
  · exact hsF _ (by omega) hk
  · exact hsF _ (by omega) (by omega)
  · exact coneFiber_structure_bijective f c hE hF hπE hπF n (k + 2) (by omega)
      (hsE _ (by omega) hk)
  · exact coneFiber_structure_bijective f c hE hF hπE hπF n (k + 1) (by omega)
      (hsE _ (by omega) (by omega))

end Topology.LoopPrespectrum
