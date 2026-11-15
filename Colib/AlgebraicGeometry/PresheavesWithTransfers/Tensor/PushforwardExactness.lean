/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Pushforward
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Projectives and the original parameter tensor

Additive precomposition is exact, since its limits and colimits are
computed on the original coefficient groups. Consequently its left
adjoint preserves projective objects. For the native parameter product,
this left adjoint agrees with the existing parameter tensor, compatibly
with its literal pure-tensor unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (F : Cor k ⥤ Cor k) [F.Additive]

instance : PreservesFiniteLimits (additivePrecompose F) := by
  let U : PresheafWithTransfers.{u + 1} k ⥤ ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) := forget
  let e : U.FullyFaithful :=
    ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})
  let : U.Full := e.full
  let : U.Faithful := e.faithful
  let hU : ReflectsLimitsOfSize.{0, 0} U := fullyFaithful_reflectsLimits U
  let : ReflectsFiniteLimits U := { reflects J _ _ := hU.reflectsLimitsOfShape (J := J) }
  have : PreservesFiniteLimits (additivePrecompose F ⋙ U) := by
    change PreservesFiniteLimits (U ⋙ (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (additivePrecompose F) U

instance : PreservesFiniteColimits (additivePrecompose F) := by
  let U : PresheafWithTransfers.{u + 1} k ⥤ ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) := forget
  let e : U.FullyFaithful :=
    ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})
  let : U.Full := e.full
  let : U.Faithful := e.faithful
  let hU : ReflectsColimitsOfSize.{0, 0} U := fullyFaithful_reflectsColimits U
  let : ReflectsFiniteColimits U := { reflects J _ _ := hU.reflectsColimitsOfShape (J := J) }
  have : PreservesFiniteColimits (additivePrecompose F ⋙ U) := by
    change PreservesFiniteColimits (U ⋙ (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (additivePrecompose F) U

instance : (coendPushforward F).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (coendPushforwardAdjunction F)

/-- An isomorphism of additive parameter functors identifies their restriction functors. -/
def additivePrecomposeNatIso {G : Cor k ⥤ Cor k} [G.Additive] (e : F ≅ G) :
    additivePrecompose F ≅ additivePrecompose G :=
  let D := additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1}
  let d : F.op ≅ G.op := (NatIso.op e).symm
  let a (P : PresheafWithTransfers.{u + 1} k) :
      (additivePrecompose F).obj P ≅ (additivePrecompose G).obj P :=
    ObjectProperty.isoMk D (Functor.isoWhiskerRight d P.obj)
  NatIso.ofComponents a (fun {P Q} f => by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    change f.hom.app (F.op.obj X) ≫ Q.obj.map (d.hom.app X) =
      P.obj.map (d.hom.app X) ≫ f.hom.app (G.op.obj X)
    exact (f.hom.naturality (d.hom.app X)).symm)

/-- The adjunctions transport pushforward along an isomorphism of parameter functors. -/
def coendPushforwardNatIso {G : Cor k ⥤ Cor k} [G.Additive] (e : F ≅ G) :
    coendPushforward F ≅ coendPushforward G :=
  ((coendPushforwardAdjunction F).ofNatIsoRight (additivePrecomposeNatIso F e)).leftAdjointUniq
    (coendPushforwardAdjunction G)

variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- On the original parameter functor, the general coend is the existing parameter tensor. -/
def coendPushforwardParameterIso :
    coendPushforward (Cor.parameterProduct T) ≅ parameterTensorFunctor T :=
  (coendPushforwardAdjunction (Cor.parameterProduct T)).leftAdjointUniq
    (parameterTensorAdjunction T)

/-- The comparison preserves the original pure-tensor adjunction unit. -/
theorem coendPushforwardParameterIso_unit (P : PresheafWithTransfers.{u + 1} k) :
    coendPushforwardUnit (Cor.parameterProduct T) P ≫
        (withParameterFunctor T).map ((coendPushforwardParameterIso T).hom.app P) =
      parameterTensorUnit T P := by
  change coendPushforwardUnit (Cor.parameterProduct T) P ≫
      (additivePrecompose (Cor.parameterProduct T)).map
        ((coendPushforwardParameterIso T).hom.app P) = parameterTensorUnit T P
  let F := Cor.parameterProduct T
  let G := additivePrecompose F
  let L := coendPushforwardAdjunction F
  let R := parameterTensorAdjunction T
  have h := Adjunction.unit_leftAdjointUniq_hom_app L R P
  change L.unit.app P ≫ G.map ((coendPushforwardParameterIso T).hom.app P) = R.unit.app P at h
  rw [coendPushforwardAdjunction_unit_app, parameterTensorAdjunction_unit_app] at h
  exact h

end AlgebraicGeometry.PresheafWithTransfers
