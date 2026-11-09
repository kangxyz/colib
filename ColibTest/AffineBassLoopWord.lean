/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed

/-! The right-associated loop word and the independent output and structure coordinates.
The outer concatenation occupies two halves; its second half is itself split in halves.
Thus the durations are one half, one quarter, one quarter, not equal thirds. -/
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum AlgebraicGeometry.Scheme.Modules
universe u
variable (R : CommRingCat.{u}) (n : ℕ) (t s : unitInterval)
variable (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n)

example : Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap R).map n x) t =
    ((boundedAboveFlatAffineSectionBassNullHomotopy R).symm.trans
      (((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (StrictSquare.comparison
          (boundedAboveFlatAffineSectionBassSquare R)))).trans
        (boundedAboveFlatAffineSectionBassNullHomotopy R))).level n (t, x) := rfl

example : Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap R).map n x) 0 =
    (boundedAboveFlatAffineSectionBassCone R).point n :=
  Path.source _
example : Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap R).map n x) 1 =
    (boundedAboveFlatAffineSectionBassCone R).point n :=
  Path.target _
example : Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap R).map (n + 1)
    ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x s)) t =
      (boundedAboveFlatAffineSectionBassCone R).structureMap n
        (Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap R).map n x) t) s :=
  congrArg (fun p ↦ Path.toContinuousMap (p s) t)
    ((boundedAboveFlatAffineSectionBassSeedMap R).comm n x)
