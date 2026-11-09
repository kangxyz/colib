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

example (hk : k < n + 2)
    (x : ((boundedAboveFlatAffineSectionBassDiagram 0).obj R).space (n + 0 + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedAboveFlatAffineSectionBassDiagram 0).obj R).space (n + 0 + 2)) x) :=
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at 0 R n k hk x

example (hk : k < n + 2)
    (x : ((boundedAboveFlatAffineSectionBassDiagram 1).obj R).space (n + 1 + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedAboveFlatAffineSectionBassDiagram 1).obj R).space (n + 1 + 2)) x) :=
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at 1 R n k hk x

example (hk : k < n + 2)
    (x : ((boundedAboveFlatAffineSectionBassDiagram 2).obj R).space (n + 2 + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedAboveFlatAffineSectionBassDiagram 2).obj R).space (n + 2 + 2)) x) :=
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at 2 R n k hk x

example (hk : k < n + 2)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (n + i + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (n + i + 2)) x) :=
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at i R n k hk x

example (m : ℕ) (hm : i + 2 ≤ m) (hk : k + i < m)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space m) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space m) x) :=
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le i R m hm k hk x

example : IsHomotopyConnectedMap
    (((boundedAboveFlatAffineSectionBassTransition i).app R).map (n + i + 3)) (n + 1) :=
  boundedAboveFlatAffineSectionBassTransition_isHomotopyConnectedMap i R n
