/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeparation

/-! Concrete T1 synthesis at zero, positive, finite Bass and quotient levels. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

variable (R : CommRingCat.{u}) (i k r : ℕ)

example : T1Space ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :=
  inferInstance

example : T1Space ((boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space (r + 1)) :=
  inferInstance

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 1).obj R).space k) :=
  inferInstance

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram 2).obj R).space k) :=
  inferInstance

example : T1Space (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :=
  inferInstance

example : T1Space ((boundedAboveFlatAffineSectionBassTelescope R).space k) :=
  inferInstance
