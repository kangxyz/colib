/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumPullback
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackCoherence

/-!
# The geometric split composition track for bounded-flat pullback

The first track realizes the actual pullback composition isomorphism. The second
is the canonical exact-functor composition normalization. This split track is not
the single total normalized transformation track.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Geometric composition followed by the actual chosen-zero composition normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/BoundedFlatPullback.lean:40-49"
  "adaptation" "The original two-part geometric and normalization track for arbitrary pullback"]
def boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    LoopPrespectrum.Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (f ≫ g))
      (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  (exactOriginalPrespectrumIsoHomotopy
    (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    ((boundedAboveFlatPerfectPullback_isExact g).comp
      (boundedAboveFlatPerfectPullback_isExact f))
    (boundedAboveFlatPerfectPullbackCompIso f g)).trans
      (exactOriginalPrespectrumMapCompHomotopy
        (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        (boundedAboveFlatPerfectPullback_isExact g)
        (boundedAboveFlatPerfectPullback_isExact f))

end AlgebraicGeometry.Scheme.Modules
