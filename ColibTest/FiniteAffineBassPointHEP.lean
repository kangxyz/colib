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

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram 0).obj R).point (0)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty 0 R (0)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 0).obj R).space (0)) :=
  inferInstance

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram 0).obj R).point (k + 1)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty 0 R (k + 1)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 0).obj R).space (k + 1)) :=
  inferInstance

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram 1).obj R).point (0)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty 1 R (0)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 1).obj R).space (0)) :=
  inferInstance

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram 1).obj R).point (k + 1)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty 1 R (k + 1)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 1).obj R).space (k + 1)) :=
  inferInstance

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram 2).obj R).point (0)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty 2 R (0)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 2).obj R).space (0)) :=
  inferInstance

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram 2).obj R).point (k + 1)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty 2 R (k + 1)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 2).obj R).space (k + 1)) :=
  inferInstance

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point (0)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R (0)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (0)) :=
  inferInstance

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point (k + 1)))) :=
  boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R (k + 1)

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (k + 1)) :=
  inferInstance


example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point 0))) :=
  boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty R 0

example : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point (k + 1)))) :=
  boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty R (k + 1)
