/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Reduced
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionParameterMap

/-! # Comparison of the original and convolution parameter maps -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K

variable {T T' : SmoothSite (Spec (.of k))}
  [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]

private theorem additivePrecomposeMap_parameterProductMap (f : T ⟶ T') :
    additivePrecomposeMap (Cor.parameterProductMap f) = parameterPullbackNatTrans k f := by
  apply NatTrans.ext
  funext P
  apply ObjectProperty.hom_ext
  rfl

/-- The native coend comparison carries the original graph parameter map
to its established adjunction mate. -/
theorem coendPushforwardParameterIso_hom_parameterMap (f : T ⟶ T') :
    coendPushforwardParameterMap (Cor.parameterProductMap f) ≫
        (coendPushforwardParameterIso T').hom =
      (coendPushforwardParameterIso T).hom ≫
        (conjugateEquiv (parameterTensorAdjunction T') (parameterTensorAdjunction T)).symm
          (parameterPullbackNatTrans k f) := by
  let G := coendPushforwardAdjunction (Cor.parameterProduct T)
  let H := coendPushforwardAdjunction (Cor.parameterProduct T')
  let A := parameterTensorAdjunction T
  let B := parameterTensorAdjunction T'
  let x := coendPushforwardParameterMap (Cor.parameterProductMap f)
  let α := parameterPullbackNatTrans k f
  let y := (conjugateEquiv B A).symm α
  let e := coendPushforwardParameterIso T
  let e' := coendPushforwardParameterIso T'
  let R : PST(k) ⥤ PST(k) := withParameterFunctor T
  let R' : PST(k) ⥤ PST(k) := withParameterFunctor T'
  apply NatTrans.ext
  funext P
  change x.app P ≫ e'.hom.app P = e.hom.app P ≫ y.app P
  apply (G.homEquiv _ _).injective
  change G.unit.app P ≫ R.map (x.app P ≫ e'.hom.app P) =
    G.unit.app P ≫ R.map (e.hom.app P ≫ y.app P)
  have h₁ : H.unit.app P ≫ α.app _ = G.unit.app P ≫ R.map (x.app P) := by
    have hα := NatTrans.congr_app (additivePrecomposeMap_parameterProductMap f)
      ((coendPushforward (Cor.parameterProduct T')).obj P)
    exact (congrArg (H.unit.app P ≫ ·) hα.symm).trans
      (unit_conjugateEquiv_symm H G (additivePrecomposeMap (Cor.parameterProductMap f)) P)
  have h₂ : B.unit.app P ≫ α.app _ = A.unit.app P ≫ R.map (y.app P) :=
    unit_conjugateEquiv_symm B A α P
  have he : G.unit.app P ≫ R.map (e.hom.app P) = A.unit.app P :=
    Adjunction.unit_leftAdjointUniq_hom_app G A P
  have he' : H.unit.app P ≫ R'.map (e'.hom.app P) = B.unit.app P :=
    Adjunction.unit_leftAdjointUniq_hom_app H B P
  calc
    _ = (H.unit.app P ≫ α.app _) ≫ R.map (e'.hom.app P) := by
      rw [R.map_comp, ← Category.assoc, ← h₁]
    _ = B.unit.app P ≫ α.app _ := by
      rw [Category.assoc, ← α.naturality, ← Category.assoc, he']
    _ = _ := by rw [R.map_comp, ← Category.assoc, he, h₂]

end AlgebraicGeometry.PresheafWithTransfers
