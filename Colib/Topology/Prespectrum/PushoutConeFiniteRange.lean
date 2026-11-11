/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.PushoutFiniteStructureRange
public import Colib.Topology.Prespectrum.ParameterLoopingFiniteStructure

/-!
# Finite-range closure under the actual Bass operation

The span-cone loses one degree of structure range. Parameter-correct looping at the
next growth level recovers that degree while raising the growth offset by one.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/PushoutConeFiniteRange.lean` at Quillen commit
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
variable {A B C D : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  (d : HomotopyPushout.prespectrum f g ⟶ D) (c : ℕ)
  (hA : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point n))))
  (hB : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point n))))
  (hC : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point n))))
  (hD : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (D.point n))))
  (hπA : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (A.space (n + c + 2)) x))
  (hπB : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (B.space (n + c + 2)) x))
  (hπC : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (C.space (n + c + 2)) x))
  (hπD : ∀ n x j, j < n + 2 →
    Subsingleton (HomotopyGroup.Pi j (D.space (n + c + 2)) x))
  (hσA : ∀ n j, 0 < j → j < 2 * n + 2 → Function.Bijective
    (HomotopyGroup.map (N := Fin j) (A.structureMap (n + c + 2)) (A.map_point _)))
  (hσB : ∀ n j, 0 < j → j < 2 * n + 2 → Function.Bijective
    (HomotopyGroup.map (N := Fin j) (B.structureMap (n + c + 2)) (B.map_point _)))
  (hσC : ∀ n j, 0 < j → j < 2 * n + 2 → Function.Bijective
    (HomotopyGroup.map (N := Fin j) (C.structureMap (n + c + 2)) (C.map_point _)))
  (hσD : ∀ n j, 0 < j → j < 2 * n + 2 → Function.Bijective
    (HomotopyGroup.map (N := Fin j) (D.structureMap (n + c + 2)) (D.map_point _)))

include hA hB hC hD hπA hπB hπC hπD hσA hσB hσC hσD

/-- The unchanged cone of a comparison from the span loses exactly one range degree. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutConeFiniteRange.lean:55"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem pushoutCone_structure_bijective_of_finite_corners (n j : ℕ)
    (hj : 0 < j) (hr : j < 2 * n + 1) :
    Function.Bijective (HomotopyGroup.map (N := Fin j)
      ((mappingCone d).structureMap (n + c + 2)) ((mappingCone d).map_point _)) := by
  have hP (m : ℕ) := HomotopyPushout.point_homotopyExtensionProperty f g m
    (hA m) (hB m) (hC m)
  have hπP (m : ℕ) (x) (k : ℕ) (hk : k < m + 2) :=
    HomotopyPushout.homotopyGroup_subsingleton f g (m + c + 2) m
      (hA _) (hB _) (hC _) (hπA m) (hπB m) (hπC m) x k hk
  by_cases hj1 : j = 1
  · subst j
    exact structure_one_bijective_of_growth (mappingCone d) c
      (mappingCone_growth d c (fun m ↦ hP _) (fun m ↦ hD _) hπP hπD) n
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  apply mappingCone_structure_bijective d c (fun m ↦ hP _) (fun m ↦ hD _)
    hπP hπD n k (2 * n + 1) (by omega) hr
  · intro t ht ht'
    exact HomotopyPushout.structure_bijective_of_finite_corners f g c hA hB hC
      hπA hπB hπC hσA hσB hσC n t ht ht'
  · intro t ht ht'
    exact hσD n t ht (by omega)

/-- Original parameter looping restores the slope-two range at offset c+1. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutConeFiniteRange.lean:78"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem loopedPushoutCone_structure_bijective_of_finite_corners (n j : ℕ)
    (hj : 0 < j) (hr : j < 2 * n + 2) :
    Function.Bijective (HomotopyGroup.map (N := Fin j)
      ((parameterLooping (mappingCone d)).structureMap (n + (c + 1) + 2))
      ((parameterLooping (mappingCone d)).map_point _)) := by
  rw [show n + (c + 1) + 2 = (n + 1) + c + 2 by omega]
  apply parameterLooping_structure_bijective
  exact pushoutCone_structure_bijective_of_finite_corners f g d c
    hA hB hC hD hπA hπB hπC hπD hσA hσB hσC hσD (n + 1) (j + 1)
    (by omega) (by omega)

end Topology.LoopPrespectrum
