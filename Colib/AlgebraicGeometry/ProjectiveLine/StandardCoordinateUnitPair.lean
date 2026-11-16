/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.NativeSingleUnitComparison

/-! # Both coordinates of the actual Laurent unit operations -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.ProjectiveLine

open AlgebraicGeometry.Scheme.Modules.CoefficientDoubleNativeUnit
attribute [local instance] Waldhausen.Additivity.KCommGroup

local notation "W" Y =>
  RingedSpace.perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace
    (Scheme.toLocallyRingedSpace Y))

set_option maxHeartbeats 600000 in
-- The original overlap map is a composite of exact functor-induced maps.
/-- Both coordinates of the actual forward Laurent unit on the literal projection. -/
@[colib_tag "COL-1291", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeGlobalUnitProjection.lean:39-55"
  "adaptation" "Both forward coordinates on the actual Laurent projection"]
theorem positiveBassForwardUnit_coordinates (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (a : (W X.obj).K n) :
    (projectiveLineKEquiv X.obj n).symm
      (PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
        (standardChart_cover X.obj) n
        (KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom) (n + 1)
          (originalKSelfTrackOperation (W X.obj) (W (Relative.laurentFunctor.obj X).obj)
            (perfectFlatUnitHomotopy (Relative.laurentProjection.app X).hom
              (relativeLaurentCoordinateUnit X)) n a))) = (a⁻¹, a) := by
  let e := (standardOverlapLaurentIso X).hom
  let f := (Relative.laurentProjection.app X).hom
  let b := (projectiveLineKEquiv X.obj n).symm.toMonoidHom.comp
    ((PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
      (standardChart_cover X.obj) n).comp
      (KMap (perfectFlatPullback_waldhausenExact e) (n + 1)))
  let y := originalKSelfTrackOperation (W X.obj) (W (Relative.laurentFunctor.obj X).obj)
    (perfectFlatUnitHomotopy f (relativeLaurentCoordinateUnit X)) n a
  change b y = _
  have h : b (positiveBassUnitSection X n a) = (a, a⁻¹) :=
    positiveBassUnitSection_coordinates X n a
  have hy : positiveBassUnitSection X n a = y⁻¹ := perfectLaurentInverseOperation_eq_inv X n a
  rw [hy, b.map_inv] at h
  exact inv_injective (h.trans (by simp))

set_option maxHeartbeats 650000 in
-- Both track operations reduce to the inclusion's stable naturality square.
private theorem boundedFlatLaurentUnit_inclusion {X Y : Scheme.{u}}
    (f : Y ⟶ X) [Flat f] (q : (Γ(Y, ⊤))ˣ) (n : ℕ)
    (x : (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).K n) :
    boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace (n + 1)
      (originalKSelfTrackOperation _ _ (boundedAboveFlatPerfectUnitHomotopy f q) n x) =
    originalKSelfTrackOperation _ _ (perfectFlatUnitHomotopy f q) n
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n x) := by
  let A := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let B := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace
  let C := perfectComplexesWaldhausen X.toRingedSpace
  let D := perfectComplexesWaldhausen Y.toRingedSpace
  let H := boundedAboveFlatPerfectUnitHomotopy f q
  let J := perfectFlatUnitHomotopy f q
  let F := (stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
    (boundedAboveFlatPerfectToPerfectPrespectrumMap Y.toRingedSpace)
  let G := (stableHomotopyFunctor (n : ℤ)).map
    (boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace)
  let y := boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n x
  let z := originalKStableEquiv A n (Additive.ofMul x)
  apply (originalKStableEquiv D (n + 1)).injective
  change originalKStableEquiv D (n + 1) (Additive.ofMul
    (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace (n + 1)
      (originalKSelfTrackOperation A B H n x))) =
    originalKStableEquiv D (n + 1)
      (Additive.ofMul (originalKSelfTrackOperation C D J n y))
  calc
    _ = F (originalKStableEquiv B (n + 1)
          (Additive.ofMul (originalKSelfTrackOperation A B H n x))) :=
      boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality _ _ _
    _ = F (H.stableOperation (n : ℤ) z) :=
      congrArg (fun a : stableHomotopyGroup (originalPrespectrum B) ((n + 1 : ℕ) : ℤ) ↦ F a)
        (originalKSelfTrackOperation_stable A B H n x)
    _ = J.stableOperation (n : ℤ) (G z) :=
      ConcreteCategory.congr_hom
        (boundedAboveFlatPerfectUnitHomotopy_stableOperation_inclusion f q (n : ℤ)) z
    _ = J.stableOperation (n : ℤ) (originalKStableEquiv C n (Additive.ofMul y)) :=
      congrArg (fun a : stableHomotopyGroup (originalPrespectrum C) (n : ℤ) ↦
        J.stableOperation (n : ℤ) a)
        (boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality _ n x).symm
    _ = _ := (originalKSelfTrackOperation_stable C D J n y).symm

/-- The literal forward operation on bounded-above flat complexes retains both coordinates
after the actual perfect inclusion. -/
@[colib_tag "COL-1291"]
theorem positiveBassBoundedFlatForwardUnit_coordinates (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ)
    (x : (boundedAboveFlatPerfectWaldhausen X.obj.toRingedSpace).K n) :
    let Y := (Relative.laurentFunctor.obj X).obj
    let f := (Relative.laurentProjection.app X).hom
    let q := relativeLaurentCoordinateUnit X
    let a := boundedAboveFlatPerfectToPerfectKMap X.obj.toRingedSpace n x
    (projectiveLineKEquiv X.obj n).symm
      (PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
        (standardChart_cover X.obj) n
        (KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom) (n + 1)
          (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace (n + 1)
            (originalKSelfTrackOperation _ _ (boundedAboveFlatPerfectUnitHomotopy f q) n x)))) =
      (a⁻¹, a) := by
  dsimp only
  rw [boundedFlatLaurentUnit_inclusion]
  exact positiveBassForwardUnit_coordinates X n _

/-- The literal inverse operation on bounded-above flat complexes retains both coordinates
after the actual perfect inclusion. -/
@[colib_tag "COL-1291"]
theorem positiveBassBoundedFlatInverseUnit_coordinates (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ)
    (x : (boundedAboveFlatPerfectWaldhausen X.obj.toRingedSpace).K n) :
    let Y := (Relative.laurentFunctor.obj X).obj
    let f := (Relative.laurentProjection.app X).hom
    let q := (relativeLaurentCoordinateUnit X)⁻¹
    let a := boundedAboveFlatPerfectToPerfectKMap X.obj.toRingedSpace n x
    (projectiveLineKEquiv X.obj n).symm
      (PerfectMayerVietoris.connectingHom (negativeChart X.obj).ι (positiveChart X.obj)
        (standardChart_cover X.obj) n
        (KMap (perfectFlatPullback_waldhausenExact (standardOverlapLaurentIso X).hom) (n + 1)
          (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace (n + 1)
            (originalKSelfTrackOperation _ _ (boundedAboveFlatPerfectUnitHomotopy f q) n x)))) =
      (a, a⁻¹) := by
  dsimp only
  rw [boundedFlatLaurentUnit_inclusion]
  exact positiveBassUnitSection_coordinates X n _

end AlgebraicGeometry.Scheme.ProjectiveLine
