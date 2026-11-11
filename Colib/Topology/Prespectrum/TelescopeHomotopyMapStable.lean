/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeHomotopyMap
public import Colib.Topology.Prespectrum.TelescopeStableColimit

/-!
# Stable invariance for homotopy-compatible telescope maps

Specified whole homotopies of the transition squares give natural maps on the
original stage stable groups. The actual telescope map constructed from these
tracks agrees with the canonical stable-colimit comparison. Stagewise stable
equivalences therefore give an original stable equivalence of telescopes,
without strictifying the diagram or choosing compatible inverse homotopies.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a : ∀ i, E i ⟶ E' i)
  (H : ∀ i, Homotopy (a i ≫ f' i) (f i ≫ a (i + 1)))

/-- Whole transition homotopies give a natural transformation of the original stable diagrams. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMapStable.lean:34"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison."]
def homotopyStageStableDiagramMap (d : ℤ) :
    stageStableDiagram E f d ⟶ stageStableDiagram E' f' d :=
  NatTrans.ofSequence (fun i ↦ (stableHomotopyFunctor d).map (a i)) (fun i ↦ by
    change (stableHomotopyFunctor d).map (transition E f i (i + 1) (Nat.le_succ i)) ≫
      (stableHomotopyFunctor d).map (a (i + 1)) =
        (stableHomotopyFunctor d).map (a i) ≫
          (stableHomotopyFunctor d).map (transition E' f' i (i + 1) (Nat.le_succ i))
    rw [transition_succ, transition_succ]
    simpa only [Functor.map_comp] using ((H i).stableHomotopyMap_eq d).symm)

/-- The stable comparison retains the actual telescope map with its supplied transition tracks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMapStable.lean:45"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison.",
  reassoc]
theorem stableColimitComparison_mapOfHomotopies (d : ℤ) :
    colimMap (homotopyStageStableDiagramMap E f E' f' a H d) ≫
        stableColimitComparison E' f' d =
      stableColimitComparison E f d ≫
        (stableHomotopyFunctor d).map (mapOfHomotopies E f E' f' a H) := by
  apply colimit.hom_ext
  intro i
  rw [ι_colimMap_assoc, stableColimitComparison_ι, stableColimitComparison_ι_assoc]
  change (stableHomotopyFunctor d).map (a i) ≫
    (stableHomotopyFunctor d).map (inclusion E' f' i) =
      (stableHomotopyFunctor d).map (inclusion E f i) ≫
        (stableHomotopyFunctor d).map (mapOfHomotopies E f E' f' a H)
  have h := congrArg ((stableHomotopyFunctor d).map)
    (inclusion_mapOfHomotopies E f E' f' a H i)
  simpa only [Functor.map_comp] using h.symm

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((E' i).space k)]

/-- The stable map with supplied tracks is the canonical conjugate of the stage-colimit map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMapStable.lean:64"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison."]
theorem stableMap_mapOfHomotopies (d : ℤ) :
    (stableHomotopyFunctor d).map (mapOfHomotopies E f E' f' a H) =
      (stableColimitIso E f d).inv ≫
        colimMap (homotopyStageStableDiagramMap E f E' f' a H d) ≫
          (stableColimitIso E' f' d).hom := by
  apply (cancel_epi (stableColimitIso E f d).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (stableColimitComparison_mapOfHomotopies E f E' f' a H d).symm

/-- Stagewise stable equivalences preserve the actual telescope for whole homotopy compatibility. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMapStable.lean:74"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison."]
theorem mapOfHomotopies_isStableEquivalence (h : ∀ i, IsStableEquivalence (a i)) :
    IsStableEquivalence (mapOfHomotopies E f E' f' a H) := by
  intro d
  let α := homotopyStageStableDiagramMap E f E' f' a H d
  have : ∀ i, IsIso (α.app i) := fun i ↦ h i d
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : IsIso (colimMap α) := by
    change IsIso (colim.map α)
    infer_instance
  rw [stableMap_mapOfHomotopies]
  change IsIso ((stableColimitIso E f d).inv ≫ colimMap α ≫ (stableColimitIso E' f' d).hom)
  infer_instance

end Topology.LoopPrespectrum.Telescope
