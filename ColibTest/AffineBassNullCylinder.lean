/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed

/-! The actual null cylinder, entire homotopy and independent structure coordinate. -/
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
variable (R : CommRingCat.{u}) (n : ℕ) (t s : unitInterval)
variable (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n)

example : boundedAboveFlatAffineSectionBassCone R =
    mappingCone (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)) := rfl
example : (boundedAboveFlatAffineSectionBassNullHomotopy R).level n (t, x) =
    ReducedMappingCone.cylinder
      ((StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R)).point n)
      ((boundedAboveFlatAffineSectionBassSquare R).right.right.point n)
      ((StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)).map n)
      (t, (StrictSquare.sourceLeg (boundedAboveFlatAffineSectionBassSquare R)).map n x) :=
  boundedAboveFlatAffineSectionBassNullHomotopy_apply R n t x
example : (boundedAboveFlatAffineSectionBassNullHomotopy R).level n (0, x) =
    (mappingConeInclusion (StrictSquare.comparison
      (boundedAboveFlatAffineSectionBassSquare R))).map n
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map
          (laurentCoefficientInclusion R)).map n x) :=
  (boundedAboveFlatAffineSectionBassNullHomotopy R).at_zero n x
example : (boundedAboveFlatAffineSectionBassNullHomotopy R).level n (1, x) =
    (boundedAboveFlatAffineSectionBassCone R).point n :=
  (boundedAboveFlatAffineSectionBassNullHomotopy R).at_one n x
example : (boundedAboveFlatAffineSectionBassNullHomotopy R).level n
    (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n) =
      (boundedAboveFlatAffineSectionBassCone R).point n :=
  (boundedAboveFlatAffineSectionBassNullHomotopy R).at_point n t
example : (boundedAboveFlatAffineSectionBassNullHomotopy R).level (n + 1)
    (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x s) =
      (boundedAboveFlatAffineSectionBassCone R).structureMap n
        ((boundedAboveFlatAffineSectionBassNullHomotopy R).level n (t, x)) s :=
  (boundedAboveFlatAffineSectionBassNullHomotopy R).comm n t x s

variable {R} {S : CommRingCat.{u}} (f : R ⟶ S)
example : (boundedAboveFlatAffineSectionBassConeMap f).map n
    ((boundedAboveFlatAffineSectionBassNullHomotopy R).level n (t, x)) =
      (boundedAboveFlatAffineSectionBassNullHomotopy S).level n
        (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map n x) :=
  boundedAboveFlatAffineSectionBassNullHomotopy_naturality_apply f n t x
example : ((boundedAboveFlatAffineSectionBassNullHomotopy R).postcomp
    (boundedAboveFlatAffineSectionBassConeMap f)).cast
      (boundedAboveFlatAffineSectionBassNullHomotopy_start_naturality f)
      (boundedAboveFlatAffineSectionBassNullHomotopy_end_naturality f) =
    (boundedAboveFlatAffineSectionBassNullHomotopy S).precomp
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f) :=
  boundedAboveFlatAffineSectionBassNullHomotopy_naturality f
