/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeparation
public import Colib.Topology.Prespectrum.TelescopeStableColimit

/-!
# The actual signed stable groups of the section Bass telescope

The original stable groups of the actual iterated Bass stages, with the iterated original
Laurent seed as connecting arrows, have a canonical colimit isomorphism onto the unchanged
stable group of the actual telescope. The comparison holds in every integer degree and is
natural for the original strict coefficient maps. All point-set hypotheses are discharged.

This does not identify these stage groups with classical Bass groups or assert a
nonconnective Thomason–Trobaugh localization theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual stable groups of the original Bass stages and their unchanged connecting arrows. -/
def boundedAboveFlatAffineSectionBassStableDiagram (R : CommRingCat.{u}) (d : ℤ) :
    ℕ ⥤ AddCommGrpCat.{u+1} :=
  Telescope.stageStableDiagram (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R) d

/-- The original strict coefficient map on the actual stage stable groups. -/
def boundedAboveFlatAffineSectionBassStableDiagramMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    (d : ℤ) : boundedAboveFlatAffineSectionBassStableDiagram R d ⟶
      boundedAboveFlatAffineSectionBassStableDiagram S d :=
  Telescope.stageStableDiagramMap
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f) d

/-- Coefficients act strictly on the entire actual stage stable diagram. -/
def boundedAboveFlatAffineSectionBassStableDiagramFunctor (d : ℤ) :
    CommRingCat.{u} ⥤ (ℕ ⥤ AddCommGrpCat.{u+1}) where
  obj R := boundedAboveFlatAffineSectionBassStableDiagram R d
  map f := boundedAboveFlatAffineSectionBassStableDiagramMap f d
  map_id R := by
    apply NatTrans.ext
    funext i
    exact (congrArg ((stableHomotopyFunctor d).map)
      ((boundedAboveFlatAffineSectionBassDiagram i).map_id R)).trans
      ((stableHomotopyFunctor d).map_id _)
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact (congrArg ((stableHomotopyFunctor d).map)
      ((boundedAboveFlatAffineSectionBassDiagram i).map_comp f g)).trans
      ((stableHomotopyFunctor d).map_comp _ _)

/-- The filtered colimit of the unchanged stage groups, with the original coefficient maps. -/
def boundedAboveFlatAffineSectionBassStableColimitFunctor (d : ℤ) :
    CommRingCat.{u} ⥤ AddCommGrpCat.{u+1} :=
  boundedAboveFlatAffineSectionBassStableDiagramFunctor d ⋙ colim

/-- The canonical comparison is an isomorphism in every signed degree, unconditionally. -/
def boundedAboveFlatAffineSectionBassStableColimitIso (R : CommRingCat.{u}) (d : ℤ) :
    colimit (boundedAboveFlatAffineSectionBassStableDiagram R d) ≅
      stableHomotopyGroup (boundedAboveFlatAffineSectionBassTelescope R) d :=
  Telescope.stableColimitIso (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R) d

/-- Each canonical stage leg maps to exactly the original telescope stage inclusion. -/
@[reassoc] theorem boundedAboveFlatAffineSectionBassStableColimitIso_ι_hom
    (R : CommRingCat.{u}) (d : ℤ) (i : ℕ) :
    colimit.ι (boundedAboveFlatAffineSectionBassStableDiagram R d) i ≫
        (boundedAboveFlatAffineSectionBassStableColimitIso R d).hom =
      (stableHomotopyFunctor d).map
        ((boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R) :=
  Telescope.stableColimitIso_ι_hom
    (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
    (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) d i

/-- The actual comparison commutes with every original strict coefficient map. -/
@[reassoc] theorem boundedAboveFlatAffineSectionBassStableColimitIso_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ) :
    colimMap (boundedAboveFlatAffineSectionBassStableDiagramMap f d) ≫
        (boundedAboveFlatAffineSectionBassStableColimitIso S d).hom =
      (boundedAboveFlatAffineSectionBassStableColimitIso R d).hom ≫
        (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap f) :=
  Telescope.stableColimitIso_naturality
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).naturality f) d

/-- The signed colimit comparison is a natural isomorphism of the actual coefficient functors. -/
def boundedAboveFlatAffineSectionBassStableColimitNatIso (d : ℤ) :
    boundedAboveFlatAffineSectionBassStableColimitFunctor d ≅
      boundedAboveFlatAffineSectionBassTelescopeFunctor ⋙ stableHomotopyFunctor d :=
  NatIso.ofComponents (fun R ↦ boundedAboveFlatAffineSectionBassStableColimitIso R d)
    (fun f ↦ boundedAboveFlatAffineSectionBassStableColimitIso_naturality f d)

/-- Every component is exactly the original canonical telescope comparison. -/
@[simp] theorem boundedAboveFlatAffineSectionBassStableColimitNatIso_hom_app
    (d : ℤ) (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineSectionBassStableColimitNatIso d).hom.app R =
      (boundedAboveFlatAffineSectionBassStableColimitIso R d).hom := rfl

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassStableColimit.lean:29-112"
  "adaptation" "Canonical signed stable colimit natural isomorphism for the actual affine tower"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableDiagram
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableDiagramMap
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableDiagramFunctor
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitFunctor
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitIso
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitIso_ι_hom
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitIso_naturality
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitNatIso
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitNatIso_hom_app

attribute [colib_tag "COL-0362"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitIso
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassStableColimitNatIso
