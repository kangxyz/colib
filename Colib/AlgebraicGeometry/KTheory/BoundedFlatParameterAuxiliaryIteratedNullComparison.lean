/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedNullComparison

/-! # The original auxiliary iterated-to-twisted whole-null square -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open SchemeNaturalSeed NaturalTrack
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original whole auxiliary null is preserved by the actual iterated/twisted comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:124"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem iterated_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((iteratedTelescope (fiberAction f T)).obj X).space n) :
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (openAction f T)).app X).map n
      (((iteratedNull f T).homotopy X).level n (r, x)) =
      ((twistedNull f T).homotopy X).level n
        (r, ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
          (fiberAction f T)).app X).map n x) :=
  SchemeIteratedSeedTelescope.null_square _ _ _ _ _ (enlargement_equivariant f T)
    (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T) X n r x

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
