/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.ConeFiniteGrowth
public import Colib.Topology.Prespectrum.FiniteFiberSourceStructure
public import Colib.Topology.Prespectrum.PushoutConeCollapse
public import Colib.Topology.Prespectrum.PushoutVanishing

/-!
# Closure of finite structure ranges under the original pushout

The original right-cone collapse transports the cone structure, and the actual fiber
ladder detects the pushout structure. The one-degree loss is retained explicitly.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/PushoutFiniteStructureRange.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C) (c : ℕ)
  (hA : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point n))))
  (hB : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point n))))
  (hC : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point n))))
  (hπA : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (A.space (n + c + 2)) x))
  (hπB : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (B.space (n + c + 2)) x))
  (hπC : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (C.space (n + c + 2)) x))
  (hσA : ∀ n j, 0 < j → j < 2 * n + 2 → Function.Bijective
    (HomotopyGroup.map (N := Fin j) (A.structureMap (n + c + 2)) (A.map_point _)))
  (hσB : ∀ n j, 0 < j → j < 2 * n + 2 → Function.Bijective
    (HomotopyGroup.map (N := Fin j) (B.structureMap (n + c + 2)) (B.map_point _)))
  (hσC : ∀ n j, 0 < j → j < 2 * n + 2 → Function.Bijective
    (HomotopyGroup.map (N := Fin j) (C.structureMap (n + c + 2)) (C.map_point _)))

include hA hB hC hπA hπB hπC hσA hσB hσC

/-- All positive chosen-point degrees of the original pushout structure in the finite range. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutFiniteStructureRange.lean:50"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem structure_bijective_of_finite_corners (n j : ℕ) (hj : 0 < j)
    (hr : j < 2 * n + 1) :
    Function.Bijective (HomotopyGroup.map (N := Fin j)
      ((prespectrum f g).structureMap (n + c + 2))
      ((prespectrum f g).map_point (n + c + 2))) := by
  have hP (m : ℕ) := point_homotopyExtensionProperty f g m (hA m) (hB m) (hC m)
  have hπP (m : ℕ) (x) (k : ℕ) (hk : k < m + 2) :=
    homotopyGroup_subsingleton f g (m + c + 2) m
      (hA _) (hB _) (hC _) (hπA m) (hπB m) (hπC m) x k hk
  by_cases hj1 : j = 1
  · subst j
    exact structure_one_bijective_of_growth (prespectrum f g) c hπP n
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hc (t : ℕ) (ht : 0 < t) (ht' : t < 2 * n + 2) :
      Function.Bijective (HomotopyGroup.map (N := Fin t)
        ((mappingCone f).structureMap (n + c + 2))
        ((mappingCone f).map_point (n + c + 2))) := by
    by_cases ht1 : t = 1
    · subst t
      exact structure_one_bijective_of_growth (mappingCone f) c
        (mappingCone_growth f c (fun m ↦ hA _) (fun m ↦ hB _) hπA hπB) n
    obtain ⟨l, rfl⟩ : ∃ l, t = l + 2 := ⟨t - 2, by omega⟩
    exact mappingCone_structure_bijective f c (fun m ↦ hA _) (fun m ↦ hB _)
      hπA hπB n l (2 * n + 2) le_rfl ht'
      (hσA n)
      (hσB n)
  have hc' (t : ℕ) (ht : 0 < t) (ht' : t < 2 * n + 2) :
      Function.Bijective (HomotopyGroup.map (N := Fin t)
        ((mappingCone (inr f g)).structureMap (n + c + 2))
        ((mappingCone (inr f g)).map_point (n + c + 2))) := by
    apply structure_bijective_of_map_target (rightConeCollapse f g) (n + c + 2) t
    · exact based_bijective_of_weak _ _
        (rightConeCollapse_level_isWeakHomotopyEquivalence f g _ (hA _) (hB _) (hC _)) t
    · exact based_bijective_of_weak _ _
        (rightConeCollapse_level_isWeakHomotopyEquivalence f g _ (hA _) (hB _) (hC _)) (t + 1)
    · exact hc t ht ht'
  apply structure_source_bijective_of_fiber (mappingConeInclusion (inr f g)) (n + c + 2) k
  · exact hc' _ (by omega) (by omega)
  · exact hc' _ (by omega) (by omega)
  · exact coneFiber_structure_bijective (inr f g) c (fun m ↦ hC _) (fun m ↦ hP _)
      hπC hπP n (k + 2) (by omega)
      (hσC n _ (by omega) (by omega))
  · exact coneFiber_structure_bijective (inr f g) c (fun m ↦ hC _) (fun m ↦ hP _)
      hπC hπP n (k + 1) (by omega)
      (hσC n _ (by omega) (by omega))

end Topology.LoopPrespectrum.HomotopyPushout
