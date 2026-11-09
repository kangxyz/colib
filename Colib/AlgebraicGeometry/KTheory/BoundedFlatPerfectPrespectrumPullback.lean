/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectFlatUnitHomotopy
public import Colib.AlgebraicGeometry.Modules.PerfectPullbackCompatibility
public import Colib.Topology.Prespectrum.HomotopyComposition

/-!
# Whole flat-pullback comparison squares

Actual termwise pullback commutes with the literal flat-to-perfect inclusion by a
functor isomorphism. Canonical zero normalization and composition homotopies give
the whole prespectrum square, without imposing a strict equality after rebasing.
The flat-model pullback exists for arbitrary morphisms; the square with exact
perfect pullback requires flatness. Neither construction requires compactness.

This is a prerequisite for, not a construction of, coefficient section models.
Implementation provenance: Quillen `PerfectComplexes/BoundedFlat/Functor.lean`
and `Waldhausen/SConstruction/Iterated/ExactCoherence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The actual normalized exact flat-model pullback, even for nonflat scheme morphisms. -/
def boundedAboveFlatPerfectPullbackPrespectrumMap (f : X ⟶ Y) :
    originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) ⟶
      originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) :=
  exactOriginalPrespectrumMap _ _ (boundedAboveFlatPerfectPullback_isExact f)

/-- The whole comparison square, including canonical zero and composition normalization. -/
def boundedAboveFlatPerfectPullbackPrespectrumHomotopy (f : X ⟶ Y) [Flat f] :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatPerfectToPerfectPrespectrumMap Y.toRingedSpace ≫ perfectFlatPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f ≫
        boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace) :=
  (exactOriginalPrespectrumMapCompHomotopy _ _ _
    (boundedAboveFlatPerfectInclusion_isExact Y.toRingedSpace)
    (perfectFlatPullback_waldhausenExact f)).symm.trans
      ((exactOriginalPrespectrumIsoHomotopy _ _
        ((boundedAboveFlatPerfectInclusion_isExact Y.toRingedSpace).comp
          (perfectFlatPullback_waldhausenExact f))
        ((boundedAboveFlatPerfectPullback_isExact f).comp
          (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace))
        (boundedAboveFlatPerfectInclusionFlatPullbackIso f)).trans
          (exactOriginalPrespectrumMapCompHomotopy _ _ _
            (boundedAboveFlatPerfectPullback_isExact f)
            (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace)))

/-- The entire comparison fixes the chosen zero at every level and homotopy time. -/
theorem boundedAboveFlatPerfectPullbackPrespectrumHomotopy_at_point
    (f : X ⟶ Y) [Flat f] (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level n
        (s, (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).point n) =
      (originalPrespectrum (perfectComplexesWaldhausen X.toRingedSpace)).point n :=
  (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).at_point n s

/-- Level, homotopy time and structure time are independent, including level zero. -/
theorem boundedAboveFlatPerfectPullbackPrespectrumHomotopy_comm
    (f : X ⟶ Y) [Flat f] (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n)
    (t : unitInterval) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level (n + 1)
        (s, (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).structureMap
          n x t) =
      (originalPrespectrum (perfectComplexesWaldhausen X.toRingedSpace)).structureMap n
        ((boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level n (s, x)) t :=
  (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).comm n s x t

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0351"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectPullbackPrespectrumHomotopy
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectPullbackPrespectrumHomotopy_at_point
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectPullbackPrespectrumHomotopy_comm
