/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedCoefficientChart

/-!
# Direct consumers of the actual mixed coefficient chart

These checks use an arbitrary parameter map, every actual graph component and the
existing native exterior point. There is no flatness assumption on the parameter
map and no compatible-component range hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow

universe u

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

example : IsOpenImmersion (nativeMixedCoefficientChart X Y T U ψ z hz t) := inferInstance

example : nativeMixedCoefficientChart X Y T U ψ z hz t ≫
    nativeMixedCoefficientPair X Y T U (integralComponentAt z) ψ =
    correspondenceSupportProductInclusion (SmoothSite.product X T).hom
      (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
      (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) ≫
      correspondenceMiddlePair (SmoothSite.product X T).hom (SmoothSite.product X U).hom
        (SmoothSite.product Y U).hom :=
  nativeMixedCoefficientChart_middlePair X Y T U ψ z hz t

example : nativeMixedCoefficientChart X Y T U ψ z hz t ≫ pullback.fst _ _ ≫
    pullback.snd X.hom T.hom =
    pullback.fst _ _ ≫ nativeParameterGraphSource X T U ψ t ≫
      pullback.snd X.hom T.hom :=
  nativeMixedCoefficientChart_second X Y T U ψ z hz t

example : nativeMixedCoefficientChart X Y T U ψ z hz t ≫ pullback.snd _ _ ≫
    pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
      U.hom =
    pullback.snd _ _ ≫ (nativeExteriorSupportIso X Y U z hz).inv ≫
      pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        U.hom :=
  nativeMixedCoefficientChart_fourth X Y T U ψ z hz t
