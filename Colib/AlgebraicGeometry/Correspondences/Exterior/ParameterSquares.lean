/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterMap
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Target

/-!
# Cartesian source and target squares for parameter changes

Both product naturality squares of the literal exterior support are Cartesian.
This is the geometric input for comparing actual graph incidences. No Tor or
cycle equality is inferred solely from these squares.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow
variable {S : Scheme.{u}} (X Y : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) {T U : SmoothSite S} (ψ : T ⟶ U)

/-- Source naturality is the genuine Cartesian square, not only commutativity. -/
theorem exteriorParameterMap_source_isPullback :
    IsPullback (exteriorParameterMap X Y W ψ) (exteriorIdentitySource X Y T W)
      (exteriorIdentitySource X Y U W) (SmoothSite.productMap (𝟙 X) ψ).left := by
  apply IsPullback.flip
  refine IsPullback.of_bot ?_ (exteriorParameterMap_source X Y W ψ).symm
    (exteriorIdentitySource_isPullback X Y U W)
  simpa [SmoothSite.productMap, SmoothSite.productLift,
    SmoothSite.productFst, SmoothSite.productSnd] using
    (exteriorIdentitySource_isPullback X Y T W)

/-- The target naturality square is Cartesian over an arbitrary base as well. -/
theorem exteriorParameterMap_target_isPullback :
    IsPullback (exteriorParameterMap X Y W ψ) (exteriorIdentityTarget X Y T W)
      (exteriorIdentityTarget X Y U W) (SmoothSite.productMap (𝟙 Y) ψ).left := by
  apply IsPullback.flip
  refine IsPullback.of_bot ?_ (exteriorParameterMap_target X Y W ψ).symm
    (exteriorIdentityTarget_isPullback X Y U W)
  simpa [SmoothSite.productMap, SmoothSite.productLift,
    SmoothSite.productFst, SmoothSite.productSnd] using
    (exteriorIdentityTarget_isPullback X Y T W)

end Stacks.Chow
