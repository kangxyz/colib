/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedCoefficientCommonList

/-! # Direct consumers on the actual mixed coefficient scheme -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open AlgebraicGeometry.Scheme Stacks.Chow

universe u

variable {S : Scheme.{u}} (X Y T U : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) (ψ : T ⟶ U)

example :
    (nativeMixedCoefficientSectionIso X Y T U W ψ).hom ≫
      pullback.fst (nativeMixedSectionProjection X U)
        (nativeMixedSupportMap X Y T U W ψ) = nativeMixedCoefficientPair X Y T U W ψ :=
  nativeMixedCoefficientSectionIso_hom_fst X Y T U W ψ

example : Smooth (nativeMixedSectionProjection X U) := inferInstance

example [IsLocallyNoetherian S] :
    IsLocallyNoetherian (exteriorIdentitySupport X Y T W) :=
  isLocallyNoetherian_nativeMixedSupport X Y T W

example [IsLocallyNoetherian S]
    (c : nativeMixedCoefficient X Y T U W) (v : (SmoothSite.product X U).left)
    (hc : nativeMixedCoefficientPair X Y T U W ψ c =
      pullback.diagonal (SmoothSite.product X U).hom v) :
    ∃ (r : ℕ) (b : Fin r →
      (pullback (SmoothSite.product X U).hom (SmoothSite.product X U).hom).presheaf.stalk
        (nativeMixedCoefficientPair X Y T U W ψ c)),
      IsRegular
        ((pullback (SmoothSite.product X U).hom (SmoothSite.product X U).hom).presheaf.stalk
          (nativeMixedCoefficientPair X Y T U W ψ c)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        (((pullback (SmoothSite.product X U).hom (SmoothSite.product X U).hom).presheaf.stalkCongr
          (.of_eq hc)).hom ≫ (pullback.diagonal (SmoothSite.product X U).hom).stalkMap v).hom ∧
      IsRegular ((nativeMixedCoefficient X Y T U W).presheaf.stalk c)
        (List.ofFn (fun i => (nativeMixedCoefficientPair X Y T U W ψ).stalkMap c (b i))) :=
  exists_nativeMixedCoefficient_common_regular_list X Y T U W ψ c v hc
