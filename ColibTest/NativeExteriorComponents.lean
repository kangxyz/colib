/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Components

/-!
# In-package checks for native exterior Components
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
noncomputable section
variable {S : Scheme.{u}} (X Y T : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)

example : Set.range (exteriorIdentitySource X Y T W) =
    (pullback.fst X.hom T.hom) ⁻¹' Set.range (exteriorSupportSourceProjection X Y W) :=
  exteriorIdentitySource_range X Y T W
example [IsFinite (exteriorSupportSourceProjection X Y W)] :
    Set.range ((exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) =
      (pullback.fst X.hom T.hom) ⁻¹' Set.range (exteriorSupportSourceProjection X Y W) :=
  exteriorIdentityImage_range X Y T W
example [GeometricallyIntegral T.hom] :
    irreducibleComponents X.left ≃ irreducibleComponents (SmoothSite.product X T).left :=
  exteriorSourceComponentsEquiv X T
example [GeometricallyIntegral T.hom] (C : irreducibleComponents X.left) :
    (exteriorSourceComponentsEquiv X T C).1 = (pullback.fst X.hom T.hom) ⁻¹' C.1 := rfl
