/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)
  (hRange : Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ⊆
    Set.range (nativeParameterGraphSource X T U ψ t))

example :
    (nativeMixedGraphIncidenceIso X Y T U ψ z hz t hRange).hom ≫
      correspondenceIncidenceMap (SmoothSite.product X T).hom (SmoothSite.product X U).hom
        (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
        (nativeExteriorPoint X Y U z hz) =
    (nativeExteriorSupportIso X Y T z hz).hom ≫
      correspondenceGraphPostcompositionMap (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Y U).hom
        (SmoothSite.productMap (𝟙 Y) ψ).left (MorphismProperty.Over.w _)
        (nativeExteriorPoint X Y T z hz) :=
  nativeMixedGraphIncidenceIso_hom_map X Y T U ψ z hz t hRange
