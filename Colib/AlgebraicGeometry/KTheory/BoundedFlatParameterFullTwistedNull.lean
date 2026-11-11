/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedNull

/-! # Original same-null comparison with the actual twisted telescope -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open KTheory.Bass.SchemeNaturalSeed KTheory.Bass.NaturalTrack
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original full-open null on the twisted telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:78"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedNull := twistedInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)


/-- The actual full-open original null is preserved at all points and all times. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:93"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem twisted_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope (supportedTrack f)).obj X).space n) :
    ((conjugacyTelescopeMap (ambientTrack P)).app X).map n
      (((normalizedNull f).homotopy X).level n (r, x)) =
      ((twistedNull f).homotopy X).level n
        (r, ((conjugacyTelescopeMap (supportedTrack f)).app X).map n x) :=
  conjugacyTelescopeMap_null _ _ _ _ _ (forget_equivariant f) (fullMap_equivariant f)
    (fullNull f) (timeSlice_equivariant f) X n r x

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
