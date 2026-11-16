/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarSelfTrackRelativeBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitTrackOperation
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization

/-!
# The scalar cone formula for the actual qcqs boundary

A scalar on the ambient scheme that restricts to a unit on the open induces
the original scalar cone after the ordinary Laurent unit operation and the
actual qcqs boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS

namespace AlgebraicGeometry.Scheme.Modules

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

theorem perfectAcyclicSupportedKEquiv_scalarConeKMap (n : ℕ) :
    (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp (perfectOpenScalarConeKMap j r q hq n) =
      perfectSupportedScalarConeKMap j r q hq n := by
  have h := KMap_comp_KMap (perfectSupportedScalarConeFunctor_waldhausenExact j r q hq)
    (perfectSupportedToAcyclic_exact j) n
  change (KMap (perfectSupportedToAcyclic_exact j) n).comp
      (perfectSupportedScalarConeKMap j r q hq n) = perfectOpenScalarConeKMap j r q hq n at h
  rw [← h]
  change (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
      ((perfectAcyclicSupportedKEquiv j n).symm.toMonoidHom.comp
        (perfectSupportedScalarConeKMap j r q hq n)) = _
  ext x
  exact (perfectAcyclicSupportedKEquiv j n).apply_symm_apply _

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  [HasDerivedCategory.{d} U.Modules]

/-- The actual qcqs boundary of the raw unit operation is the literal supported scalar cone. -/
theorem perfectQcqsConnectingHom_comp_scalarUnitOperation (n : ℕ) :
    (perfectQcqsConnectingHom j n).comp
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) (perfectFlatUnitHomotopy j q) n) =
      perfectSupportedScalarConeKMap j r q hq n := by
  rw [← perfectOpenScalarOriginalKOperation_restrict j r q hq n, ← MonoidHom.comp_assoc]
  change ((perfectQcqsConnectingHom j n).comp (perfectOpenKRestrict j (n + 1))).comp _ = _
  rw [perfectQcqsConnectingHom_comp_relative,
    perfectOpenConnectingHom_comp_scalarOriginalSelfTrack,
    perfectAcyclicSupportedKEquiv_scalarConeKMap]

end AlgebraicGeometry.Scheme.Modules
