/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Additive

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

example (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    nativeExterior X Y T (singleFiniteCorrespondence X.hom Y.hom z hz (-3)) =
      (-3 : ℤ) • nativeExteriorPrime X Y T z hz :=
  nativeExterior_single X Y T z hz (-3)
example (α β : finiteCorrespondences X.hom Y.hom) :
    nativeExterior X Y T (α + β) = nativeExterior X Y T α + nativeExterior X Y T β :=
  nativeExterior_add X Y T α β
