/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeHomotopyMapStable

/-!
# Stable extensionality for original telescope maps

Finite original stable representatives detect equality of homomorphisms induced
by maps out of the actual reduced telescope. Thus changing whole transition
tracks does not change the induced signed stable-group map, and the actual
track-defined maps obey identity and composition laws on those groups.
These statements do not assert point-set homotopies or higher coherence of
the telescope maps themselves. Only the source stages require T1 levels.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  [∀ i k, T1Space ((E i).space k)]

/-- Original stage inclusions jointly detect equality of induced signed stable-group maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeStableMapExt.lean:32"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem stableMap_ext {F : LoopPrespectrum.{u}} (a b : prespectrum E f ⟶ F) (d : ℤ)
    (h : ∀ i, (stableHomotopyFunctor d).map (inclusion E f i ≫ a) =
      (stableHomotopyFunctor d).map (inclusion E f i ≫ b)) :
    (stableHomotopyFunctor d).map a = (stableHomotopyFunctor d).map b := by
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨i, y, rfl⟩ := exists_stable_representative E f d x
  have hi := h i
  simp only [Functor.map_comp] at hi
  exact ConcreteCategory.congr_hom hi y

/-- The original stable map is independent of the chosen whole transition homotopies. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeStableMapExt.lean:44"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem stableMap_mapOfHomotopies_eq
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i)
    (H K : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1))) (d : ℤ) :
    (stableHomotopyFunctor d).map (mapOfHomotopies E f F g a H) =
      (stableHomotopyFunctor d).map (mapOfHomotopies E f F g a K) := by
  apply stableMap_ext E f
  intro i
  rw [inclusion_mapOfHomotopies, inclusion_mapOfHomotopies]

/-- Identity stage maps with arbitrary supplied tracks induce the genuine identity stable map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeStableMapExt.lean:55"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem stableMap_mapOfHomotopies_id
    (H : ∀ i, Homotopy (𝟙 (E i) ≫ f i) (f i ≫ 𝟙 (E (i + 1)))) (d : ℤ) :
    (stableHomotopyFunctor d).map (mapOfHomotopies E f E f (fun i ↦ 𝟙 (E i)) H) =
      𝟙 (stableHomotopyGroup (prespectrum E f) d) := by
  calc
    _ = (stableHomotopyFunctor d).map (𝟙 (prespectrum E f)) := by
      apply stableMap_ext E f
      intro i
      rw [inclusion_mapOfHomotopies, Category.id_comp, Category.comp_id]
    _ = _ := (stableHomotopyFunctor d).map_id _

/-- Composition holds on the original stable groups for any supplied compatible composite tracks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeStableMapExt.lean:67"
  "adaptation" "Original stagewise stable extensionality and unchanged telescope tail maps."]
theorem stableMap_mapOfHomotopies_comp
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
    (H : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1)))
    (K : ∀ i, Homotopy (b i ≫ h i) (g i ≫ b (i + 1)))
    (L : ∀ i, Homotopy ((a i ≫ b i) ≫ h i) (f i ≫ (a (i + 1) ≫ b (i + 1))))
    (d : ℤ) :
    (stableHomotopyFunctor d).map (mapOfHomotopies E f F g a H) ≫
        (stableHomotopyFunctor d).map (mapOfHomotopies F g G h b K) =
      (stableHomotopyFunctor d).map
        (mapOfHomotopies E f G h (fun i ↦ a i ≫ b i) L) := by
  rw [← Functor.map_comp]
  apply stableMap_ext E f
  intro i
  rw [← Category.assoc, inclusion_mapOfHomotopies, Category.assoc,
    inclusion_mapOfHomotopies, inclusion_mapOfHomotopies, Category.assoc]

end Topology.LoopPrespectrum.Telescope
