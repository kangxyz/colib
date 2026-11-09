/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeparation
public import Colib.KTheory.Bass.StrictDiagramPointHEP
public import Colib.KTheory.Waldhausen.Iterated.PointHEP

/-!
# Point HEP of every actual affine-section Bass stage

Every original section S-prespectrum level has HEP at its literal chosen point, including
the degree-zero loop space. The actual strict Bass iteration propagates this property
using the existing native T1 separation, without extra premises at later stages.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTopology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Every original section S-point has genuine HEP, including its literal zero-level loop. -/
theorem boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (k : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point k))) :=
  Waldhausen.IteratedS.prespectrum_point_homotopyExtensionProperty
    (boundedAboveFlatAffineSectionModel R) k

/-- Every chosen point at every iterated stage remains genuinely well-based. -/
theorem boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty
    (i : ℕ) (R : CommRingCat.{u}) (k : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point k))) :=
  KTheory.Bass.strictDiagramIterate_point_homotopyExtensionProperty
    CommRingCat.PolynomialLaurent.laurentSquareFunctor i
    boundedAboveFlatAffineSectionPrespectrumFunctor
    boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty R k

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTopology.lean:32"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTopology.lean:46"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty

attribute [colib_tag "COL-0375"]
  boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty

end AlgebraicGeometry.Scheme.Modules
