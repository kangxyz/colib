/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorZero
public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceIso
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic

/-!
# Matched mixed incidence has degree-zero multiplicity one

The compatible-component range condition identifies the actual mixed incidence
with the full exterior support W × T. Here W is the original integral component
and T is smooth, so native geometric reducedness and flat base change make that
support reduced. No geometric integrality of T or perfectness of the field is
needed. At a generic incidence point the full local ring has length one.

The degree-zero pair Tor is identified as an ambient module with this full
incidence stalk by `correspondenceIncidenceAmbientTorZeroIso`. Its length is
therefore one; this is not a Tor equality or length-one provider assumption.
The geometric input applies native Stacks 056T and the reduced generic-stalk
length theorem, independently of any positive-degree vanishing proof.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)
  (hRange : Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ⊆
    Set.range (nativeParameterGraphSource X T U ψ t))

include hRange

/-- Compatible actual graph incidence is reduced by the smooth parameter projection. -/
@[stacks 056T "application: smooth parameter gives reduced full support and matched incidence"]
theorem isReduced_nativeMixedGraphIncidence :
    IsReduced (nativeMixedGraphIncidence X Y T U ψ z hz t) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (show X.left ⟶ Spec (.of k) from X.hom)
  have : IsLocallyNoetherian (pullback X.hom Y.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst X.hom Y.hom)
  have : IsLocallyNoetherian (integralComponentAt z).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt z).subschemeι
  have : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  have : GeometricallyReduced T.hom := geometricallyReduced_of_smooth T.hom
  have : IsReduced (exteriorIdentitySupport X Y T (integralComponentAt z)) :=
    inferInstanceAs (IsReduced (pullback
      (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom) T.hom))
  exact isReduced_of_isOpenImmersion
    (nativeMixedGraphIncidenceIso X Y T U ψ z hz t hRange).inv

/-- At an actual generic matched-incidence point, original ambient Tor in degree zero
has length one. -/
theorem length_nativeMixedGraphIncidenceAmbientTor_zero_eq_one
    (x : nativeMixedGraphIncidence X Y T U ψ z hz t) (hx : IsMax x) :
    Module.length
      (correspondenceIncidenceAmbientStalk (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
        (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x)
      (correspondenceIncidenceAmbientTor (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
        (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x 0) = 1 := by
  rw [length_correspondenceIncidenceAmbientTor_zero]
  have : IsReduced (nativeMixedGraphIncidence X Y T U ψ z hz t) :=
    isReduced_nativeMixedGraphIncidence X Y T U ψ z hz t hRange
  exact length_stalk_eq_one_of_isMax hx

/-- The same degree-zero multiplicity over the actual support ring with its canonical Tor action. -/
theorem length_nativeMixedGraphIncidenceSupportTor_zero_eq_one
    (x : nativeMixedGraphIncidence X Y T U ψ z hz t) (hx : IsMax x) :
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
        (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x 0) = 1 := by
  let := correspondenceIncidenceTorSupportModule (SmoothSite.product X T).hom
    (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
    (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x 0
  exact (correspondenceIncidenceTor_length_eq_support (SmoothSite.product X T).hom
    (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
    (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x 0).symm.trans
      (length_nativeMixedGraphIncidenceAmbientTor_zero_eq_one X Y T U ψ z hz t hRange x hx)

end Stacks.Chow
