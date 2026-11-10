/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedCoefficientExchange

/-!
# Consumers of the literal mixed coefficient/graph exchange

The first checks work over any base and with any closed support. The final check
composes the new exchange with the actual native support-product open chart,
without assuming flatness of the parameter morphism or a component-range match.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow

universe u

section General

variable {S : Scheme.{u}} (X Y T U : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) (ψ : T ⟶ U)

example : nativeMixedCoefficientPair X Y T U W ψ ≫ (nativeMixedMiddleSwap X U).hom =
    (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ nativeMixedGraphPair X Y T U W ψ :=
  nativeMixedCoefficientPair_exchange X Y T U W ψ

example : pullback.diagonal (SmoothSite.product X U).hom ≫
    (nativeMixedMiddleSwap X U).hom = pullback.diagonal (SmoothSite.product X U).hom :=
  diagonal_nativeMixedMiddleSwap X U

example : nativeMixedCoefficientEmbedding X Y T U W ψ ≫
    nativeMixedCoefficientPair X Y T U W ψ =
    nativeMixedSupportMap X Y T U W ψ ≫ pullback.diagonal (SmoothSite.product X U).hom :=
  nativeMixedCoefficientEmbedding_pair X Y T U W ψ

end General

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

example : nativeMixedCoefficientChart X Y T U ψ z hz t ≫
    nativeMixedCoefficientPair X Y T U (integralComponentAt z) ψ ≫
      (nativeMixedMiddleSwap X U).hom =
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫
      (nativeMixedCoefficientGraphIso X Y T U (integralComponentAt z) ψ).hom ≫
        nativeMixedGraphPair X Y T U (integralComponentAt z) ψ := by
  rw [nativeMixedCoefficientPair_exchange]
