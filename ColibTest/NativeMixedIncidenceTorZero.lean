/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceTorZero

/-! # Matched-component degree zero with no additional parameter-integrality assumption -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)
  (hRange : Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ⊆
    Set.range (nativeParameterGraphSource X T U ψ t))

example : IsReduced (nativeMixedGraphIncidence X Y T U ψ z hz t) :=
  isReduced_nativeMixedGraphIncidence X Y T U ψ z hz t hRange

example (x : nativeMixedGraphIncidence X Y T U ψ z hz t) (hx : IsMax x) :
    Module.length
      (correspondenceIncidenceAmbientStalk (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
        (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x)
      (correspondenceIncidenceAmbientTor (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
        (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x 0) = 1 :=
  length_nativeMixedGraphIncidenceAmbientTor_zero_eq_one X Y T U ψ z hz t hRange x hx

example (x : nativeMixedGraphIncidence X Y T U ψ z hz t) (hx : IsMax x) :
    letI := correspondenceIncidenceTorSupportModule (SmoothSite.product X T).hom
      (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
      (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x 0
    Module.length
      ((correspondenceSupportProduct (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
        (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz)).presheaf.stalk
          (correspondenceIncidenceToSupportProduct (SmoothSite.product X T).hom
            (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
            (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x))
      (correspondenceIncidenceAmbientTor (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
        (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x 0) = 1 :=
  length_nativeMixedGraphIncidenceSupportTor_zero_eq_one X Y T U ψ z hz t hRange x hx
