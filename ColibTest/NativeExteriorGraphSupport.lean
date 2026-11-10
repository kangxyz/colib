/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphSupport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {S : Scheme.{u}} (X Y T : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) (φ : X ⟶ Y)
  (hW : exteriorSupportSourceProjection X Y W ≫ φ.left =
    exteriorSupportTargetProjection X Y W)
include hW

example : exteriorIdentitySource X Y T W ≫ (SmoothSite.productMap φ (𝟙 T)).left =
    exteriorIdentityTarget X Y T W :=
  exteriorIdentitySource_graph X Y T W φ hW
example [IsFinite (exteriorSupportSourceProjection X Y W)] :
    (exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          (SmoothSite.productMap φ (𝟙 T)).left =
      (exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom :=
  exteriorIdentityImage_graph X Y T W φ hW
