/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ParameterMates
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedConvolution
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated

/-! # Naturality of convolution with the native represented parameter maps -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
  [HasDerivedCategory.{w} (TransferCoefficients k)]

local notation "PST" => TransferCoefficients k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "P(" G ")" => projectiveDerivedMinusFunctor k G
local notation "p(" f ")" => projectiveDerivedMinusFunctorMap f
local notation "c" => ComplexShape.up ℤ

/-- Natural transformations between the same termwise functors agree
after passing to the chosen projective models. -/
theorem projectiveDerivedMinusFunctorIso_naturality
    {A A' B B' : PST ⥤ PST} [A.Additive] [A'.Additive] [B.Additive] [B'.Additive]
    (e : A ≅ A') (d : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B') (h : f ≫ d.hom = e.hom ≫ g)
    (K : D) :
    (p(f)).app K ≫ (projectiveDerivedMinusFunctorIso d).hom.app K =
      (projectiveDerivedMinusFunctorIso e).hom.app K ≫ (p(g)).app K := by
  let V := DerivedCategory.Minus.ι (C := PST)
  let Q := DerivedCategory.Qh (C := PST)
  let I := (boundedAboveProjectiveEquivalence k).inverse ⋙ (boundedAboveProjectiveCondition k).ι
  let ff := (Functor.FullyFaithful.ofFullyFaithful V).whiskeringRight D
  have he := NatTrans.congr_app (ff.map_preimage (X := P(A)) (Y := P(A'))
    (Functor.whiskerLeft I (Functor.whiskerRight (NatIso.mapHomotopyCategory e c).hom Q))) K
  have hd := NatTrans.congr_app (ff.map_preimage (X := P(B)) (Y := P(B'))
    (Functor.whiskerLeft I (Functor.whiskerRight (NatIso.mapHomotopyCategory d c).hom Q))) K
  change V.map ((projectiveDerivedMinusFunctorIso e).hom.app K) =
    Q.map ((e.hom.mapHomotopyCategory c).app (I.obj K)) at he
  change V.map ((projectiveDerivedMinusFunctorIso d).hom.app K) =
    Q.map ((d.hom.mapHomotopyCategory c).app (I.obj K)) at hd
  apply V.map_injective
  rw [V.map_comp, V.map_comp, he, hd, projectiveDerivedMinusFunctorMap_map_app,
    projectiveDerivedMinusFunctorMap_map_app, ← Q.map_comp, ← Q.map_comp]
  apply Q.congr_map
  have h' := congrArg (fun t => t.mapHomotopyCategory c) h
  rw [NatTrans.mapHomotopyCategory_comp, NatTrans.mapHomotopyCategory_comp] at h'
  exact NatTrans.congr_app h' (I.obj K)

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ Y, (F.obj Y).Additive]

local instance (T : Cor k) : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) T

variable {T T' : SmoothSite (Spec (.of k))}
  [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]

local notation "L(" T ")" => Cor.parameterProduct T
set_option quotPrecheck false in
local notation "R(" T ")" => (singleDerivedMinus k 0).obj ((representableLarge k).obj (Cor.mk T))

private theorem comp_right_parameter_iso_naturality
    {D₀ : Type*} [Category* D₀] {X Y Z X' Y' Z' : D₀}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (e : X ⟶ Y) (d : Y ⟶ Z) (e' : X' ⟶ Y') (d' : Y' ⟶ Z')
    (he : f ≫ e' = e ≫ g) (hd : g ≫ d' = d ≫ h) :
    f ≫ (e' ≫ d') = (e ≫ d) ≫ h :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d') he).trans
    ((Category.assoc _ _ _).trans ((congrArg (e ≫ ·) hd).trans (Category.assoc _ _ _).symm)))

omit [HasDerivedCategory PST] [∀ Y, (F.obj Y).Additive] in
private theorem nativeParameterCoefficientComparison_naturality
    (e : F.flip.obj (Cor.mk T) ≅ L(T)) (d : F.flip.obj (Cor.mk T') ≅ L(T'))
    (f : T ⟶ T') (hf : F.flip.map ((Cor.graphFunctor k).map f) ≫ d.hom =
      e.hom ≫ Cor.parameterProductMap f) :
    coendPushforwardParameterMap (F.flip.map ((Cor.graphFunctor k).map f)) ≫
        (coendPushforwardNatIso (F.flip.obj (Cor.mk T')) d ≪≫ coendPushforwardParameterIso T').hom =
      (coendPushforwardNatIso (F.flip.obj (Cor.mk T)) e ≪≫ coendPushforwardParameterIso T).hom ≫
        (conjugateEquiv (parameterTensorAdjunction T') (parameterTensorAdjunction T)).symm
          (parameterPullbackNatTrans k f) := by
  exact comp_right_parameter_iso_naturality _ _ _ _ _ _ _
    (coendPushforwardNatIso_parameterMap e d _ _ hf)
    (coendPushforwardParameterIso_hom_parameterMap f)

set_option maxHeartbeats 650000 in
-- Compare the squares on the exact same projective representatives.
/-- The comparison to the native parameter tensor takes an ordinary
parameter map to the original left mate of restriction. -/
theorem derivedConvolutionNativeParameterIso_naturality
    (e : F.flip.obj (Cor.mk T) ≅ L(T)) (d : F.flip.obj (Cor.mk T') ≅ L(T'))
    (f : T ⟶ T') (hf : F.flip.map ((Cor.graphFunctor k).map f) ≫ d.hom =
      e.hom ≫ Cor.parameterProductMap f) (K : D) :
    ((derivedConvolution F).obj K).map
        ((singleDerivedMinus k 0).map ((representableLarge k).map ((Cor.graphFunctor k).map f))) ≫
        (derivedConvolutionNativeParameterIso F T' d).hom.app K =
      (derivedConvolutionNativeParameterIso F T e).hom.app K ≫
        (p((conjugateEquiv (parameterTensorAdjunction T') (parameterTensorAdjunction T)).symm
          (parameterPullbackNatTrans k f))).app K := by
  let b := coendPushforwardNatIso (F.flip.obj (Cor.mk T)) e ≪≫ coendPushforwardParameterIso T
  let b' := coendPushforwardNatIso (F.flip.obj (Cor.mk T')) d ≪≫ coendPushforwardParameterIso T'
  let u := coendPushforwardParameterMap (F.flip.map ((Cor.graphFunctor k).map f))
  let v := (conjugateEquiv (parameterTensorAdjunction T') (parameterTensorAdjunction T)).symm
    (parameterPullbackNatTrans k f)
  let x := ((derivedConvolution F).obj K).map
    ((singleDerivedMinus k 0).map ((representableLarge k).map ((Cor.graphFunctor k).map f)))
  let y := (p(u)).app K
  let z := (p(v)).app K
  let g := (derivedConvolutionParameterIso F (Cor.mk T)).hom.app K
  let g' := (derivedConvolutionParameterIso F (Cor.mk T')).hom.app K
  let j := (projectiveDerivedMinusFunctorIso b).hom.app K
  let j' := (projectiveDerivedMinusFunctorIso b').hom.app K
  have h : u ≫ b'.hom = b.hom ≫ v :=
    nativeParameterCoefficientComparison_naturality F e d f hf
  have h₁ : x ≫ g' = g ≫ y :=
    derivedConvolutionParameterIso_naturality_right F ((Cor.graphFunctor k).map f) K
  have h₂ : y ≫ j' = j ≫ z :=
    projectiveDerivedMinusFunctorIso_naturality b b' u v h K
  change x ≫ (g' ≫ j') = (g ≫ j) ≫ z
  exact comp_right_parameter_iso_naturality x y z g j g' j' h₁ h₂

end AlgebraicGeometry.PresheafWithTransfers
