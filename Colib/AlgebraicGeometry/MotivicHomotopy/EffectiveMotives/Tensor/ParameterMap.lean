/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterA1Descent
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.EffectiveLocalization
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardParameterMap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveCoefficientMap

/-! # Effective maps of smooth parameters -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option quotPrecheck false in
local notation "q" => singularPresheafToEffective k
variable {T : SmoothSite (Spec (.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

variable {T' : SmoothSite (Spec (.of k))} {F' : Cor k ⥤ Cor k} [F'.Additive]
  (e' : Cor.graphFunctor k ⋙ F' ≅
    SmoothSite.Contraction.parameterProduct T' ⋙ Cor.graphFunctor k)

/-- A natural transformation of parameters acts through the original coend mate
and the effective localization. -/
def effectiveParameterTensorMap (f : F ⟶ F') :
    effectiveParameterTensor e ⟶ effectiveParameterTensor e' := by
  let A := derivedParameterPushforward F ⋙ q
  let B := derivedParameterPushforward F' ⋙ q
  let : Localization.Lifting q (effectivePresheafEquivalences k) A (effectiveParameterTensor e) :=
    ⟨effectiveParameterTensorCompIso e⟩
  let : Localization.Lifting q (effectivePresheafEquivalences k) B (effectiveParameterTensor e') :=
    ⟨effectiveParameterTensorCompIso e'⟩
  exact Localization.liftNatTrans q (effectivePresheafEquivalences k) A B
    (effectiveParameterTensor e) (effectiveParameterTensor e')
    (Functor.whiskerRight (projectiveDerivedMinusFunctorMap (coendPushforwardParameterMap f)) q)

/-- On a localized projective source, the map of parameters uses the actual coend mate. -/
theorem effectiveParameterTensorMap_app_localized (f : F ⟶ F')
    (K : DerivedCategory.Minus (TransferCoefficients k)) :
    (effectiveParameterTensorMap e e' f).app ((q).obj K) =
      (effectiveParameterTensorCompIso e).hom.app K ≫
        (q).map ((projectiveDerivedMinusFunctorMap (coendPushforwardParameterMap f)).app K) ≫
        (effectiveParameterTensorCompIso e').inv.app K := by
  unfold effectiveParameterTensorMap
  rw [Localization.liftNatTrans_app]
  rfl

end AlgebraicGeometry.MotivicHomotopy
