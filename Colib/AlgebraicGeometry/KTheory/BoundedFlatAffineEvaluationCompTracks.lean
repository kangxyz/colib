/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoherence

/-!
# The two affine evaluation composition tracks

These are the original direct and iterated coefficient routes. The iterated track
retains the strict section-composition and association transports.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
local notation "P" => boundedAboveFlatAffinePullbackModelMap
local notation "coefficientTrack" => boundedAboveFlatAffineEvaluationCoefficientHomotopy
local notation "C" => boundedAboveFlatAffinePullbackCompHomotopy
local notation "a" => boundedAboveFlatAffineSectionPrespectrumFunctor.map
local notation "ε" => boundedAboveFlatAffineEvaluationPrespectrumMap

/-- First compare the composite coefficient, then apply its normalized composition track. -/
def boundedAboveFlatAffineEvaluationCompDirectHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    LoopPrespectrum.Homotopy (a (f ≫ g) ≫ ε T)
      (ε R ≫ (prespectrumMap (P f) ≫ prespectrumMap (P g))) :=
  (coefficientTrack (f ≫ g)).trans (LoopPrespectrum.Homotopy.precomp (ε R) (C f g))

/-- Compare the second coefficient before the first, retaining source and associativity casts. -/
def boundedAboveFlatAffineEvaluationCompIteratedHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    LoopPrespectrum.Homotopy (a (f ≫ g) ≫ ε T)
      (ε R ≫ (prespectrumMap (P f) ≫ prespectrumMap (P g))) :=
  (((LoopPrespectrum.Homotopy.precomp (a f) (coefficientTrack g)).cast
      rfl (Category.assoc _ _ _).symm).trans
    ((coefficientTrack f).postcomp (prespectrumMap (P g)))).cast
      (by rw [← Category.assoc, ← boundedAboveFlatAffineSectionPrespectrumFunctor_map_comp])
      (Category.assoc _ _ _)

end AlgebraicGeometry.Scheme.Modules
