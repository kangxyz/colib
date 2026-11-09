/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeparation
public import Colib.Topology.Prespectrum.TelescopeConeStableColimit

/-!
# The actual coefficient-map cone of the section Bass telescope

The unchanged telescope coefficient map has its original cone strictly identified with the
original telescope of finite-stage coefficient cones. Genuine T1 at every actual Bass stage
then gives the canonical signed cone-group colimit isomorphism, retaining each original stage
cone map. No connectivity of the full telescope is assumed.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTelescopeCone.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The actual transitions of the finite-stage coefficient cones use the original iterated seed.
-/
def boundedAboveFlatAffineSectionBassConeTransition (i : ℕ) :
    mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f) ⟶
      mappingCone ((boundedAboveFlatAffineSectionBassDiagram (i + 1)).map f) :=
  Telescope.coneTransition
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f) i

/-- The original finite-stage cone map uses the unchanged two telescope inclusions. -/
def boundedAboveFlatAffineSectionBassConeStageMap (i : ℕ) :
    mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f) ⟶
      mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f) :=
  Telescope.coneStageMap
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f) i

/-- The unchanged coefficient-map cone is strictly the actual telescope of coefficient cones.
-/
def boundedAboveFlatAffineSectionBassTelescopeConeIso :
    mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f) ≅
      Telescope.prespectrum
        (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
        (boundedAboveFlatAffineSectionBassConeTransition f) :=
  Telescope.coneIso
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f)

/-- Actual signed cone groups are canonically the colimit of original finite-stage cone groups.
-/
def boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso (d : ℤ) :
    colimit (Telescope.stageStableDiagram
      (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
      (boundedAboveFlatAffineSectionBassConeTransition f) d) ≅
        stableHomotopyGroup (mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f)) d :=
  Telescope.coneStableColimitIso
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f) d

/-- Each original cone inclusion is the canonical stage map on the actual signed colimit. -/
@[reassoc] theorem boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom
    (d : ℤ) (i : ℕ) :
    colimit.ι (Telescope.stageStableDiagram
        (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
        (boundedAboveFlatAffineSectionBassConeTransition f) d) i ≫
      (boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso f d).hom =
        (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassConeStageMap f i) :=
  Telescope.coneStableColimitIso_ι_hom
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f) d i

/-- Every actual signed telescope-cone class is represented by an unchanged finite-stage cone.
-/
theorem boundedAboveFlatAffineSectionBassTelescopeCone_exists_stable_representative (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap f)) d) :
    ∃ i : ℕ, ∃ z : stableHomotopyGroup
      (mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f)) d,
      (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassConeStageMap f i) z = x := by
  let e := boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso f d
  let : PreservesFilteredColimitsOfSize.{0, 0} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨i, z, hz⟩ := Concrete.colimit_exists_rep
    (Telescope.stageStableDiagram
      (fun i ↦ mappingCone ((boundedAboveFlatAffineSectionBassDiagram i).map f))
      (boundedAboveFlatAffineSectionBassConeTransition f) d) (e.inv x)
  refine ⟨i, z, ?_⟩
  have hstage := ConcreteCategory.congr_hom
    (boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom f d i) z
  have hx := ConcreteCategory.congr_hom e.inv_hom_id x
  exact hstage.symm.trans ((congrArg e.hom hz).trans hx)


attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/\
    SectionBassTelescopeCone.lean:28-114" "adaptation"
  "Actual telescope cone interchange, signed boundary and exactness with unchanged maps"]
  boundedAboveFlatAffineSectionBassConeTransition
  boundedAboveFlatAffineSectionBassConeStageMap
  boundedAboveFlatAffineSectionBassTelescopeConeIso
  boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso
  boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom
  boundedAboveFlatAffineSectionBassTelescopeCone_exists_stable_representative

attribute [colib_tag "COL-0376"]
  boundedAboveFlatAffineSectionBassConeTransition
  boundedAboveFlatAffineSectionBassConeStageMap
  boundedAboveFlatAffineSectionBassTelescopeConeIso
  boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso
  boundedAboveFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom
  boundedAboveFlatAffineSectionBassTelescopeCone_exists_stable_representative

end AlgebraicGeometry.Scheme.Modules
