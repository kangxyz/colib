/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeConeStableColimit
public import Colib.Topology.Prespectrum.ConeStableNaturality

/-!
# The actual signed boundary of a strict telescope cone

The original finite-stage signed cone boundaries form a natural transformation by their proved
strict-square naturality. Their actual sequential colimit, conjugated by the canonical original
source and cone colimit isomorphisms, gives a boundary on the unchanged telescope cone. Its
stage formula retains the original finite boundary and original telescope inclusion.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/TelescopeConeBoundary.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    (h : ∀ i, IsStableEquivalence (mappingConeFiberComparison (a i)))

/-- The original signed boundaries commute with the original strict successor cone squares. -/
def coneBoundaryDiagramMap (d : ℤ) :
    stageStableDiagram (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) (d + 1) ⟶
      stageStableDiagram E f d :=
  NatTrans.ofSequence (fun i ↦ stableMappingConeConnecting (a i) (h i) d) (by
    intro i
    change (stableHomotopyFunctor (d + 1)).map
      ((Functor.ofSequence (coneTransition E f F g a ha)).map (homOfLE (Nat.le_succ i))) ≫ _ =
        _ ≫ (stableHomotopyFunctor d).map ((Functor.ofSequence f).map (homOfLE (Nat.le_succ i)))
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
    exact stableMappingConeConnecting_naturality
      (coneTransitionSquare E f F g a ha i) (h i) (h (i + 1)) d)

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]

/-- Descend the original finite boundaries to the unchanged telescope cone's signed stable groups.
-/
def coneStableConnecting (d : ℤ) :
    stableHomotopyGroup (mappingCone (map E f F g a ha)) (d + 1) ⟶
      stableHomotopyGroup (prespectrum E f) d :=
  (coneStableColimitIso E f F g a ha (d + 1)).inv ≫
    colimMap (coneBoundaryDiagramMap E f F g a ha h d) ≫ (stableColimitIso E f d).hom

/-- The actual boundary at every original cone stage is exactly its existing signed boundary.
-/
@[reassoc] theorem coneStableConnecting_stage (d : ℤ) (i : ℕ) :
    (stableHomotopyFunctor (d + 1)).map (coneStageMap E f F g a ha i) ≫
      coneStableConnecting E f F g a ha h d =
        stableMappingConeConnecting (a i) (h i) d ≫
          (stableHomotopyFunctor d).map (inclusion E f i) := by
  erw [← coneStableColimitIso_ι_hom, Category.assoc, coneStableConnecting,
    Iso.hom_inv_id_assoc, ι_colimMap_assoc]
  change stableMappingConeConnecting (a i) (h i) d ≫
    colimit.ι (stageStableDiagram E f d) i ≫ stableColimitComparison E f d = _
  exact congrArg (fun b ↦ stableMappingConeConnecting (a i) (h i) d ≫ b)
    (stableColimitComparison_ι E f d i)

end Topology.LoopPrespectrum.Telescope

attribute [colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeConeBoundary.lean:32-66" "adaptation"
  "Actual telescope cone interchange, signed boundary and exactness with unchanged maps"]
  Topology.LoopPrespectrum.Telescope.coneBoundaryDiagramMap
  Topology.LoopPrespectrum.Telescope.coneStableConnecting
  Topology.LoopPrespectrum.Telescope.coneStableConnecting_stage

attribute [colib_tag "COL-0376"]
  Topology.LoopPrespectrum.Telescope.coneBoundaryDiagramMap
  Topology.LoopPrespectrum.Telescope.coneStableConnecting
  Topology.LoopPrespectrum.Telescope.coneStableConnecting_stage
