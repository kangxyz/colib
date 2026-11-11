/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumPullback

/-! # The original global-unit whole homotopy of geometric bounded-flat pullback -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Realize the actual unit automorphism using the original chosen-zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnit.lean:24-30"
  "adaptation" "Whole original bounded-flat geometric unit track at every level"]
def boundedAboveFlatPerfectUnitHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    Topology.LoopPrespectrum.Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectPullback_isExact f) (boundedAboveFlatPerfectPullback_isExact f)
    (boundedAboveFlatPerfectPullbackUnitIso f r)

end AlgebraicGeometry.Scheme.Modules
