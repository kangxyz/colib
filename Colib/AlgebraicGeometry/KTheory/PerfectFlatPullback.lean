/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullbackRestriction

/-! # Waldhausen exactness of genuine flat geometric pullback

The native ambient monomorphisms, quasi-isomorphisms and pushouts are preserved by actual
termwise flat pullback. No strict representative or additional comparison is supplied.
Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/FlatPullback.lean:54-66`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Genuine flat pullback preserves the native perfect-complex Waldhausen structures. -/
theorem perfectFlatPullback_waldhausenExact {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Waldhausen.IsExact (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectFlatPullback f) := by
  let F := (pullback f).mapHomologicalComplex (ComplexShape.up ℤ)
  let P : ObjectProperty (CochainComplex Y.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)
  let Q : ObjectProperty (CochainComplex X.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
  have : PreservesFiniteLimits (pullback f) := pullback_preservesFiniteLimits_of_flat f
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero Q.ι
    exact F.map_isZero
      ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
        (Waldhausen.complexes Y.Modules) P
        (RingedSpace.perfectComplexes_cofibrationClosed Y.toRingedSpace)).zero hZ)
  · intro K L s hs
    change Mono (F.map s.hom)
    have : Mono (C := CochainComplex Y.Modules ℤ) s.hom := hs
    infer_instance
  · intro K L s hs
    change QuasiIso (F.map s.hom)
    have : QuasiIso (C := Y.Modules) s.hom := hs
    infer_instance
  · intro A B D T i g k j hi h
    apply IsPushout.of_map_of_faithful Q.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes Y.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed Y.toRingedSpace) hi h).map F

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "AlgebraicGeometry/PerfectComplexes/FlatPullback.lean:53-66"
  "adaptation" "Actual native Waldhausen exactness of genuinely flat geometric pullback"]
  AlgebraicGeometry.Scheme.Modules.perfectFlatPullback_waldhausenExact
