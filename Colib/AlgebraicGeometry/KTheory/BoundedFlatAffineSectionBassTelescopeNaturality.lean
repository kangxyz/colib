/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTelescopeExcision
public import Colib.Topology.Prespectrum.ConeStableNaturality

/-!
# Original Bass telescope cone boundaries on coefficient squares

Every original commuting coefficient square induces the unchanged strict cone map and preserves
its signed boundary. Genuine telescope excision has already been discharged for both rows.
Stable equivalences on the two original sides consequently induce a stable cone equivalence.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTelescopeNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {A B : Arrow CommRingCat.{u}} (sq : A ⟶ B)

/-- The original coefficient square on the actual strict Bass telescopes. -/
def boundedAboveFlatAffineSectionBassTelescopeSquare :
    Arrow.mk (boundedAboveFlatAffineSectionBassTelescopeMap A.hom) ⟶
      Arrow.mk (boundedAboveFlatAffineSectionBassTelescopeMap B.hom) :=
  boundedAboveFlatAffineSectionBassTelescopeFunctor.mapArrow.map sq

/-- The unchanged cone map induced by the original telescope coefficient square. -/
def boundedAboveFlatAffineSectionBassTelescopeConeMap :
    mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap A.hom) ⟶
      mappingCone (boundedAboveFlatAffineSectionBassTelescopeMap B.hom) :=
  mappingConeMap (boundedAboveFlatAffineSectionBassTelescopeSquare sq)

/-- The actual signed telescope boundary is natural for every original coefficient square. -/
@[reassoc] theorem boundedAboveFlatAffineSectionBassTelescopeConeConnecting_naturality (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatAffineSectionBassTelescopeConeMap sq) ≫
      boundedAboveFlatAffineSectionBassTelescopeConeConnecting B.hom d =
        boundedAboveFlatAffineSectionBassTelescopeConeConnecting A.hom d ≫
          (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap sq.left) :=
  stableMappingConeConnecting_naturality (boundedAboveFlatAffineSectionBassTelescopeSquare sq)
    (boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence A.hom)
    (boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence B.hom) d

/-- Stable original telescope side maps induce a stable unchanged cone map. -/
theorem boundedAboveFlatAffineSectionBassTelescopeConeMap_isStableEquivalence
    (hl : IsStableEquivalence (boundedAboveFlatAffineSectionBassTelescopeMap sq.left))
    (hr : IsStableEquivalence (boundedAboveFlatAffineSectionBassTelescopeMap sq.right)) :
    IsStableEquivalence (boundedAboveFlatAffineSectionBassTelescopeConeMap sq) :=
  mappingConeMap_isStableEquivalence_of_excision
    (boundedAboveFlatAffineSectionBassTelescopeSquare sq)
    (boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence A.hom)
    (boundedAboveFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence B.hom) hl hr


attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/\
    SectionBassTelescopeNaturality.lean:26-56" "adaptation"
  "Actual telescope cone interchange, signed boundary and exactness with unchanged maps"]
  boundedAboveFlatAffineSectionBassTelescopeSquare
  boundedAboveFlatAffineSectionBassTelescopeConeMap
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting_naturality
  boundedAboveFlatAffineSectionBassTelescopeConeMap_isStableEquivalence

attribute [colib_tag "COL-0376"]
  boundedAboveFlatAffineSectionBassTelescopeSquare
  boundedAboveFlatAffineSectionBassTelescopeConeMap
  boundedAboveFlatAffineSectionBassTelescopeConeConnecting_naturality
  boundedAboveFlatAffineSectionBassTelescopeConeMap_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules
