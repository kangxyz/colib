/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeParameter
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedCoefficientIsoShift
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalSingleRight

/-! # The signed shift of native parameter convolution -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

set_option maxHeartbeats 1250000 in
-- Compose the already supplied shift identities without searching for past edges.
private theorem parameterComposite_commShift {C₀ C₁ C₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    (Q : C₀ ⥤ C₁) (A : C₀ ⥤ C₂) (R : C₂ ⥤ C₁)
    [Q.CommShift ℤ] [A.CommShift ℤ] [R.CommShift ℤ]
    {L L' : C₁ ⥤ C₁} [L.CommShift ℤ] [L'.CommShift ℤ]
    {P₀ P₁ P₂ P₃ : C₀ ⥤ C₀}
    [P₀.CommShift ℤ] [P₁.CommShift ℤ] [P₂.CommShift ℤ] [P₃.CommShift ℤ]
    (v : L ⟶ L') (m : Q ⋙ L' ⟶ P₀ ⋙ Q)
    (t : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (u : Q ⟶ A ⋙ R)
    (hv : NatTrans.CommShift v ℤ) (hm : NatTrans.CommShift m ℤ)
    (ht : NatTrans.CommShift t ℤ) (hb : NatTrans.CommShift b ℤ)
    (hc : NatTrans.CommShift c ℤ) (hu : NatTrans.CommShift u ℤ)
    {z : Q ⋙ L ⟶ P₃ ⋙ A ⋙ R}
    (hz : z = Functor.whiskerLeft Q v ≫ m ≫ Functor.whiskerRight t Q ≫
      Functor.whiskerRight b Q ≫ Functor.whiskerRight c Q ≫
        Functor.whiskerLeft P₃ u) : NatTrans.CommShift z ℤ := by
  let := hv
  let := ht
  let := hb
  let := hc
  let := hu
  let v₀ := Functor.whiskerLeft Q v
  let t₀ := Functor.whiskerRight t Q
  let b₀ := Functor.whiskerRight b Q
  let c₀ := Functor.whiskerRight c Q
  let u₀ := Functor.whiskerLeft P₃ u
  let hv₀ : NatTrans.CommShift v₀ ℤ := NatTrans.CommShift.whiskerLeft (F₁ := Q) L L' v ℤ
  let ht₀ : NatTrans.CommShift t₀ ℤ := NatTrans.CommShift.whiskerRight t Q ℤ
  let hb₀ : NatTrans.CommShift b₀ ℤ := NatTrans.CommShift.whiskerRight b Q ℤ
  let hc₀ : NatTrans.CommShift c₀ ℤ := NatTrans.CommShift.whiskerRight c Q ℤ
  let hu₀ : NatTrans.CommShift u₀ ℤ :=
    NatTrans.CommShift.whiskerLeft (F₁ := P₃) Q (A ⋙ R) u ℤ
  have h₁ : NatTrans.CommShift (c₀ ≫ u₀) ℤ :=
    @NatTrans.CommShift.comp _ _ _ _ _ _ _ c₀ u₀ ℤ _ _ _ _ _ _ hc₀ hu₀
  have h₂ : NatTrans.CommShift (b₀ ≫ c₀ ≫ u₀) ℤ :=
    @NatTrans.CommShift.comp _ _ _ _ _ _ _ b₀ (c₀ ≫ u₀) ℤ _ _ _ _ _ _ hb₀ h₁
  have h₃ : NatTrans.CommShift (t₀ ≫ b₀ ≫ c₀ ≫ u₀) ℤ :=
    @NatTrans.CommShift.comp _ _ _ _ _ _ _ t₀ (b₀ ≫ c₀ ≫ u₀) ℤ _ _ _ _ _ _ ht₀ h₂
  have h₄ : NatTrans.CommShift (m ≫ t₀ ≫ b₀ ≫ c₀ ≫ u₀) ℤ :=
    @NatTrans.CommShift.comp _ _ _ _ _ _ _ m (t₀ ≫ b₀ ≫ c₀ ≫ u₀) ℤ
      _ _ _ _ _ _ hm h₃
  have h₅ : NatTrans.CommShift (v₀ ≫ m ≫ t₀ ≫ b₀ ≫ c₀ ≫ u₀) ℤ :=
    @NatTrans.CommShift.comp _ _ _ _ _ _ _ v₀ (m ≫ t₀ ≫ b₀ ≫ c₀ ≫ u₀) ℤ
      _ _ _ _ _ _ hv₀ h₄
  exact hz.symm ▸ h₅

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => EffectiveMotivesMinus k
set_option quotPrecheck false in
local notation "q" => singularPresheafToEffective k
local notation "a" => derivedNisnevichSheafification k
local notation "M" => effectiveMotive k
local notation "r" => effectiveReflection k
local notation "F" => curriedTensor (Cor k)
set_option quotPrecheck false in
local notation "R(" T ")" => (singleDerivedMinus k 0).obj ((representableLarge k).obj (Cor.mk T))

/-- The abelian structure of the transfer sheaves for the signed parameter comparison. -/
local instance signedParameterSheafAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

set_option quotPrecheck false in
local notation "N(" T ")" => projectiveDerivedMinusFunctor k (parameterTensorFunctor T)
local notation "Nₑ(" T ")" => N(T) ⋙ a ⋙ r

set_option maxHeartbeats 1100000 in
-- Evaluate the original convolution and coefficient maps at the chosen localized object.
private theorem effectiveNativeParameterCompIso_hom_app
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] (d : (F).flip.obj (Cor.mk T) ≅ Cor.parameterProduct T) (X : D) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    let A := (representableLarge k).obj (Cor.mk T)
    letI : ((convolutionBifunctor F).flip.obj A).Additive := convolutionBifunctor_flip_additive A
    letI := (effectiveSignedConvolutionLocalizationCoreMonoidal e).toMonoidal
    let K := R(T)
    let I := localizedRepresentableIso (Cor.mk T)
    let C := Functor.Monoidal.commTensorRight q K
    let t := derivedConvolutionSingleRightIso A
    let g := convolutionParameterNatIso F (Cor.mk T)
    let j := coendPushforwardNatIso ((F).flip.obj (Cor.mk T)) d ≪≫
      coendPushforwardParameterIso T
    let b := projectiveDerivedMinusFunctorIso g
    let c := projectiveDerivedMinusFunctorIso j
    let u := sheafificationEffectiveReflectionIso k
    let v := (curriedTensor E).flip.map I.inv
    (effectiveNativeParameterCompIso e T d).hom.app X =
      v.app ((q).obj X) ≫ C.hom.app X ≫ (q).map (t.hom.app X) ≫
        (q).map (b.hom.app X) ≫ (q).map (c.hom.app X) ≫ u.inv.app ((N(T)).obj X) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let A := (representableLarge k).obj (Cor.mk T)
  let : ((convolutionBifunctor F).flip.obj A).Additive := convolutionBifunctor_flip_additive A
  let := (effectiveSignedConvolutionLocalizationCoreMonoidal e).toMonoidal
  let K := R(T)
  let I := localizedRepresentableIso (Cor.mk T)
  let C := Functor.Monoidal.commTensorRight q K
  let g := convolutionParameterNatIso F (Cor.mk T)
  let j := coendPushforwardNatIso ((F).flip.obj (Cor.mk T)) d ≪≫ coendPushforwardParameterIso T
  let b := projectiveDerivedMinusFunctorIso g
  let c := projectiveDerivedMinusFunctorIso j
  let u := sheafificationEffectiveReflectionIso k
  let v := (curriedTensor E).flip.map I.inv
  let p := v.app ((q).obj X)
  let f := ((derivedConvolutionTensorIso (k := k)).hom.app X).app K
  let f' := (projectiveDerivedMinusBifunctorSingleRightIso (convolutionBifunctor F) A).hom.app X
  let x := C.hom.app X
  let y := b.hom.app X
  let z := c.hom.app X
  let ℓ := u.inv.app ((N(T)).obj X)
  change (p ≫ x ≫ (q).map f) ≫ (q).map ((f' ≫ y) ≫ z) ≫ ℓ =
    p ≫ x ≫ (q).map (f ≫ f') ≫ (q).map y ≫ (q).map z ≫ ℓ
  have h₀ : (q).map f ≫ (q).map (f' ≫ y ≫ z) =
      (q).map (f ≫ f') ≫ (q).map y ≫ (q).map z := by
    calc
      _ = (q).map (f ≫ f' ≫ y ≫ z) := ((q).map_comp _ _).symm
      _ = (q).map ((f ≫ f') ≫ y ≫ z) := (q).congr_map (Category.assoc _ _ _).symm
      _ = _ := ((q).map_comp _ _).trans
        (congrArg ((q).map (f ≫ f') ≫ ·) ((q).map_comp _ _))
  simp only [Category.assoc]
  exact congrArg (fun h => p ≫ x ≫ h)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ℓ) h₀)).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((q).map (f ≫ f') ≫ ·) (Category.assoc _ _ _))))

set_option maxHeartbeats 1650000 in
-- Use the native localization and projective comparisons with their chosen shifts.
set_option synthInstance.maxHeartbeats 90000 in
-- Use the tensorator and the two original coefficient comparisons in their given order.
/-- The effective right-parameter comparison preserves the first-variable signed shift. -/
theorem effectiveNativeParameterCompIso_commShift
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] (d : (F).flip.obj (Cor.mk T) ≅ Cor.parameterProduct T) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionCommShift₂Int e
    NatTrans.CommShift (effectiveNativeParameterCompIso e T d).hom ℤ := by
  let m := effectiveSignedConvolutionMonoidalCategory e
  let := m
  let shiftE := effectiveSignedConvolutionCommShift₂Int e
  let := shiftE
  let shiftD := derivedConvolutionCommShift₂Int (k := k)
  let := shiftD
  let C₀ := effectiveSignedConvolutionLocalizationCoreMonoidal e
  let := C₀.toMonoidal
  let hC₀ := effectiveSignedConvolutionLocalizationMonoidalCommShift e
  let A := (representableLarge k).obj (Cor.mk T)
  let : ((convolutionBifunctor F).flip.obj A).Additive := convolutionBifunctor_flip_additive A
  let K := R(T)
  let I := localizedRepresentableIso (Cor.mk T)
  let C := Functor.Monoidal.commTensorRight q K
  let t := derivedConvolutionSingleRightIso A
  let g := convolutionParameterNatIso F (Cor.mk T)
  let j := coendPushforwardNatIso ((F).flip.obj (Cor.mk T)) d ≪≫ coendPushforwardParameterIso T
  let b := projectiveDerivedMinusFunctorIso g
  let c := projectiveDerivedMinusFunctorIso j
  let u := sheafificationEffectiveReflectionIso k
  let v := (curriedTensor E).flip.map I.inv
  let v₀ := Functor.whiskerLeft q v
  let t₀ := Functor.whiskerRight t.hom q
  let b₀ := Functor.whiskerRight b.hom q
  let c₀ := Functor.whiskerRight c.hom q
  let u₀ := Functor.whiskerLeft N(T) u.inv
  let U : q ⋙ tensorRight ((M).obj (Cor.mk T)) ⟶ Nₑ(T) :=
    v₀ ≫ C.hom ≫ t₀ ≫ b₀ ≫ c₀ ≫ u₀
  have h : (effectiveNativeParameterCompIso e T d).hom = U := by
    apply NatTrans.ext
    funext X
    exact effectiveNativeParameterCompIso_hom_app e T d X
  let hC : NatTrans.CommShift C.hom ℤ := hC₀.commShift_μNatTransFst K
  let ht : NatTrans.CommShift t.hom ℤ := derivedConvolutionSingleRightIso_commShift A
  let hb : NatTrans.CommShift b.hom ℤ := projectiveDerivedMinusFunctorIso_commShift g
  let hc : NatTrans.CommShift c.hom ℤ := projectiveDerivedMinusFunctorIso_commShift j
  let : NatTrans.CommShift u.hom ℤ := Functor.CommShift.ofIso_compatibility u ℤ
  let hu : NatTrans.CommShift u.inv ℤ := NatTrans.CommShift.of_iso_inv u ℤ
  let hv : NatTrans.CommShift v ℤ := shiftE.commShift_flip_map I.inv
  exact parameterComposite_commShift q a r v C.hom t.hom b.hom c.hom u.inv hv hC ht hb hc hu h

end AlgebraicGeometry.MotivicHomotopy
