/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescope
public import Colib.KTheory.Waldhausen.Iterated.Separation
public import Colib.KTheory.Bass.StrictDiagramSeparation
public import Colib.Topology.Prespectrum.TelescopeSeparation

/-!
# Separation of the actual affine-section Bass telescope

T1 separation starts at the original Waldhausen realization (and its based path space in
level zero). Native finite Bass separation propagates it to every actual iterate. The actual
reduced quotient telescope is therefore T1, without any point HEP or embedding premise.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Every original section prespectrum level is T1, including its degree-zero path space. -/
instance boundedAboveFlatAffineSectionPrespectrumSpaceT1Space (R : CommRingCat.{u}) (k : ℕ) :
    T1Space ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space k) :=
  CategoryTheory.Waldhausen.IteratedS.prespectrumSpaceT1Space
    (boundedAboveFlatAffineSectionModel R) k

/-- Actual finite Bass iteration preserves the proved separation at all levels. -/
instance boundedAboveFlatAffineSectionBassDiagramSpaceT1Space
    (i : ℕ) (R : CommRingCat.{u}) (k : ℕ) :
    T1Space (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :=
  KTheory.Bass.strictDiagramIterateSpaceT1Space
    CommRingCat.PolynomialLaurent.laurentSquareFunctor i
    boundedAboveFlatAffineSectionPrespectrumFunctor R k

/-- The quotient telescope has T1 levels, with no externally supplied separation profile. -/
instance boundedAboveFlatAffineSectionBassTelescopeSpaceT1Space
    (R : CommRingCat.{u}) (k : ℕ) :
    T1Space ((boundedAboveFlatAffineSectionBassTelescope R).space k) :=
  LoopPrespectrum.Telescope.spaceT1Space
    (fun i ↦ (boundedAboveFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedAboveFlatAffineSectionBassTransition i).app R) k

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTopology.lean:27-29,40-43,55-58"
  "adaptation" "Only T1 separation of actual section stages and their reduced quotient telescope"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionPrespectrumSpaceT1Space
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassDiagramSpaceT1Space
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTelescopeSpaceT1Space

attribute [colib_tag "COL-0362"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassDiagramSpaceT1Space
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTelescopeSpaceT1Space
