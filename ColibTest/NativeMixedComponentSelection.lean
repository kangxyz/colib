/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedComponentSelection

/-! # Unique actual component selection without a matching-range provider -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

include hz in
omit [GeometricallyIntegral U.hom] in
example : ∃! t : genericPoints (SmoothSite.product X T).left,
    Set.range (nativeParameterGraphSource X T U ψ t) =
      Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) :=
  existsUnique_nativeParameterGraphComponent_matching X Y T z hz U ψ

example : exteriorIdentitySupport X Y T (integralComponentAt z) ≅
    nativeMixedGraphIncidence X Y T U ψ z hz (nativeMixedMatchingComponent X Y T z hz) :=
  nativeMixedMatchingComponentIncidenceIso X Y T z hz U ψ

example (t : genericPoints (SmoothSite.product X T).left)
    (ht : t ≠ nativeMixedMatchingComponent X Y T z hz) :
    IsEmpty (nativeMixedGraphIncidence X Y T U ψ z hz t) :=
  nativeMixedGraphIncidence_isEmpty_of_ne_matching X Y T z hz U ψ t ht

example (t : genericPoints (SmoothSite.product X T).left)
    (ht : t ≠ nativeMixedMatchingComponent X Y T z hz) :
    incidenceTorCorrespondence (SmoothSite.product X T).hom (SmoothSite.product X U).hom
      (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
      (nativeExteriorPoint X Y U z hz)
      (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.productMap (𝟙 X) ψ).left
        (MorphismProperty.Over.w _) t)
      (nativeExteriorPoint_admissible X Y U z hz) = 0 :=
  nativeMixedGraphIncidenceTor_eq_zero_of_ne_matching X Y T z hz U ψ t ht
