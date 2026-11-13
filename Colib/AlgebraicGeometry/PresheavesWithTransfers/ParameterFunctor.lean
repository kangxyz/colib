/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian

/-! # Exact parameter reindexing of transfer presheaves -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The original coefficient reindexing, functorial in the transfer presheaf. -/
def withParameterFunctor (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k where
  obj P := withParameter P T
  map η := withParameterMap η T
  map_id _ := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    rfl

variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

instance : (withParameterFunctor T :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k).Additive where
  map_add := by
    intro P Q f g
    apply ObjectProperty.hom_ext
    rfl

instance : PreservesFiniteLimits (withParameterFunctor T :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k) := by
  let U : PresheafWithTransfers.{v} k ⥤ ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) := forget
  let e : U.FullyFaithful :=
    ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v})
  let : U.Full := e.full
  let : U.Faithful := e.faithful
  let hU : ReflectsLimitsOfSize.{0, 0} U := fullyFaithful_reflectsLimits U
  let : ReflectsFiniteLimits U := { reflects J _ _ := hU.reflectsLimitsOfShape (J := J) }
  have : PreservesFiniteLimits (withParameterFunctor T ⋙ U) := by
    change PreservesFiniteLimits
      (U ⋙ (Functor.whiskeringLeft _ _ _).obj (Cor.parameterProduct T).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (withParameterFunctor T) U

instance : PreservesFiniteColimits (withParameterFunctor T :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k) := by
  let U : PresheafWithTransfers.{v} k ⥤ ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) := forget
  let e : U.FullyFaithful :=
    ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v})
  let : U.Full := e.full
  let : U.Faithful := e.faithful
  let hU : ReflectsColimitsOfSize.{0, 0} U := fullyFaithful_reflectsColimits U
  let : ReflectsFiniteColimits U := { reflects J _ _ := hU.reflectsColimitsOfShape (J := J) }
  have : PreservesFiniteColimits (withParameterFunctor T ⋙ U) := by
    change PreservesFiniteColimits
      (U ⋙ (Functor.whiskeringLeft _ _ _).obj (Cor.parameterProduct T).op)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (withParameterFunctor T) U

end AlgebraicGeometry.PresheafWithTransfers
