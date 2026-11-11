/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientSeed
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCoefficientSeedNaturality

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSupportedSection
open GlobalSectionChangeIndex

/-- The original null/unit/null seed commutes with the actual integral Spec comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientSeedCompatibility.lean:24"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem seed_square (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) ≫
        bassComparison Q =
      rowComparison Q ≫ (globalLaurentAction Q).track.seed := by
  apply NatTrans.ext
  funext a
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, bassComparison_app]
  have h := SchemeCoefficientSeedNaturality.seed_naturality
    (ParameterLaurentTrack.ambientTrack Q.left) (globalLaurentAction Q).track
    (specUnder.obj a) a (squareComparison Q a) (squareComparison_track Q a)
  rw [squareComparison_source] at h
  exact h

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

