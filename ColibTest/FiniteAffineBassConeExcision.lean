/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassConeExcision

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
variable (R S : CommRingCat.{u}) (i j n k : ℕ)

section
variable (f : (boundedAboveFlatAffineSectionBassDiagram i).obj R ⟶
  (boundedAboveFlatAffineSectionBassDiagram j).obj S)

example : IsHomotopyConnectedMap
    ((mappingConeFiberComparison f).map (n + max i j + 2)) (2 * n + 2) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap i j R S f n

example : IsIso ((stableHomotopyFunctor (-1)).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f (-1)

example : IsIso ((stableHomotopyFunctor 0).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f 0

example : IsIso ((stableHomotopyFunctor 1).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f 1

example (d : ℤ) : IsIso ((stableHomotopyFunctor d).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f d

end

section
variable (f : (boundedAboveFlatAffineSectionBassDiagram 0).obj R ⟶
  (boundedAboveFlatAffineSectionBassDiagram 2).obj S)

example : IsHomotopyConnectedMap
    ((mappingConeFiberComparison f).map (n + max 0 2 + 2)) (2 * n + 2) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap 0 2 R S f n

example : IsIso ((stableHomotopyFunctor (-1)).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 0 2 R S f (-1)

example : IsIso ((stableHomotopyFunctor 0).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 0 2 R S f 0

example : IsIso ((stableHomotopyFunctor 1).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 0 2 R S f 1

example (d : ℤ) : IsIso ((stableHomotopyFunctor d).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 0 2 R S f d

end

section
variable (f : (boundedAboveFlatAffineSectionBassDiagram 2).obj R ⟶
  (boundedAboveFlatAffineSectionBassDiagram 1).obj S)

example : IsHomotopyConnectedMap
    ((mappingConeFiberComparison f).map (n + max 2 1 + 2)) (2 * n + 2) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap 2 1 R S f n

example : IsIso ((stableHomotopyFunctor (-1)).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 2 1 R S f (-1)

example : IsIso ((stableHomotopyFunctor 0).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 2 1 R S f 0

example : IsIso ((stableHomotopyFunctor 1).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 2 1 R S f 1

example (d : ℤ) : IsIso ((stableHomotopyFunctor d).map (mappingConeFiberComparison f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence 2 1 R S f d

end

example (f : R ⟶ S) : IsStableEquivalence
    (mappingConeFiberComparison ((boundedAboveFlatAffineSectionBassDiagram i).map f)) :=
  boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f

example : IsStableEquivalence
    (mappingConeFiberComparison ((boundedAboveFlatAffineSectionBassTransition i).app R)) :=
  boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence i R

example (f : (boundedAboveFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedAboveFlatAffineSectionBassDiagram j).obj S)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) (t : unitInterval) :
    ((mappingConeFiberComparison f).map k x).1.2 t =
      ReducedMappingCone.cylinder
        (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point k)
        (((boundedAboveFlatAffineSectionBassDiagram j).obj S).point k) (f.map k) (t, x) :=
  mappingConeFiberComparison_path f k x t

example (f : R ⟶ S) : IsHomotopyConnectedMap
    ((mappingConeFiberComparison ((boundedAboveFlatAffineSectionBassDiagram i).map f)).map
      (n + max i i + 2)) (2 * n + 2) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap
    i i R S ((boundedAboveFlatAffineSectionBassDiagram i).map f) n

example : IsHomotopyConnectedMap
    ((mappingConeFiberComparison ((boundedAboveFlatAffineSectionBassTransition i).app R)).map
      (n + max i (i + 1) + 2)) (2 * n + 2) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap
    i (i + 1) R R ((boundedAboveFlatAffineSectionBassTransition i).app R) n

example (f : (boundedAboveFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedAboveFlatAffineSectionBassDiagram j).obj S) :
    mappingConeFiberComparison f ≫ homotopyFiberProjection (mappingConeInclusion f) = f :=
  mappingConeFiberComparison_projection f

example : IsStableEquivalence
    (mappingConeFiberComparison (boundedAboveFlatAffineSectionBassSeed.app R)) :=
  boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence 0 R
