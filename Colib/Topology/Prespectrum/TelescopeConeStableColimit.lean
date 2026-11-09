/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeConeIso
public import Colib.Topology.Prespectrum.TelescopeStableColimit
public import Colib.Topology.Prespectrum.ConeLoopSeparation

/-!
# Actual stable groups of the cone of a telescope map

For T1 source and target stages, the original cone-stage inclusions induce a canonical signed
stable-group colimit isomorphism onto the cone of the unchanged telescope map. The proof uses
the strict two-coordinate cone/telescope interchange and accepted compact representability;
no uniform connectivity of the telescope or stable cone exactness premise is used.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/TelescopeConeStableColimit.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]

/-- The actual stage-cone stable colimit is the signed stable group of the original telescope cone.
-/
def coneStableColimitIso (d : ℤ) :
    colimit (stageStableDiagram (fun i ↦ mappingCone (a i))
      (coneTransition E f F g a ha) d) ≅ stableHomotopyGroup (mappingCone (map E f F g a ha)) d :=
  (stableColimitIso (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) d).trans
    ((stableHomotopyFunctor d).mapIso (coneIso E f F g a ha).symm)

/-- The isomorphism is induced by the unchanged original stage-cone maps, in every signed degree.
-/
@[reassoc] theorem coneStableColimitIso_ι_hom (d : ℤ) (i : ℕ) :
    colimit.ι (stageStableDiagram (fun i ↦ mappingCone (a i))
        (coneTransition E f F g a ha) d) i ≫ (coneStableColimitIso E f F g a ha d).hom =
      (stableHomotopyFunctor d).map (coneStageMap E f F g a ha i) := by
  change colimit.ι _ i ≫ stableColimitComparison _ _ d ≫
    (stableHomotopyFunctor d).map (coneFromTelescope E f F g a ha) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b ↦ b ≫ (stableHomotopyFunctor d).map (coneFromTelescope E f F g a ha))
      (stableColimitComparison_ι (fun i ↦ mappingCone (a i))
        (coneTransition E f F g a ha) d i)).trans
      (((stableHomotopyFunctor d).map_comp _ _).symm.trans
        (congrArg ((stableHomotopyFunctor d).map)
          (inclusion_desc (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha)
            (coneStageMap E f F g a ha) (coneStageTrack E f F g a ha) i))))

end Topology.LoopPrespectrum.Telescope

attribute [colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeConeStableColimit.lean:34-51" "adaptation"
  "Actual telescope cone interchange, signed boundary and exactness with unchanged maps"]
  Topology.LoopPrespectrum.Telescope.coneStableColimitIso
  Topology.LoopPrespectrum.Telescope.coneStableColimitIso_ι_hom

attribute [colib_tag "COL-0376"]
  Topology.LoopPrespectrum.Telescope.coneStableColimitIso
  Topology.LoopPrespectrum.Telescope.coneStableColimitIso_ι_hom
