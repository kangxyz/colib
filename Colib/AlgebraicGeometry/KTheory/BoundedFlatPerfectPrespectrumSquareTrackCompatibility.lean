/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitSquare

/-! # The original geometric square track with explicit endpoint transport

The existing native square is already defined with the literal endpoint cast, so no new square
or choice of homotopy is needed. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SquareTrackCompatibility.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original geometric square retains both complete composition tracks, with an explicit
transport at their common endpoint. -/
theorem boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_level {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) (n : ℕ) :
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h).level n =
      ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy p v).symm.trans
        ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q w).cast
          (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap h).symm rfl)).level n := rfl

end AlgebraicGeometry.Scheme.Modules
