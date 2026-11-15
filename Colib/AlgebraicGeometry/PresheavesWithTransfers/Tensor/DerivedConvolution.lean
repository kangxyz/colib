/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionParameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionRepresentable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingle
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated

/-!
# Derived integral convolution

The native signed totalization derives the integral convolution. On a
represented degree-zero right argument it agrees with the projective
derived pushforward along the corresponding right parameter functor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ

variable [HasDerivedCategory.{w} PST(k)]

/-- An isomorphism of coefficient functors induces their projective derived comparison. -/
def projectiveDerivedMinusFunctorIso {L R : PST(k) ⥤ PST(k)} [L.Additive] [R.Additive]
    (e : L ≅ R) : projectiveDerivedMinusFunctor k L ≅ projectiveDerivedMinusFunctor k R := by
  let U := (boundedAboveProjectiveCondition k).ι
  let ff := Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Minus.ι (C := PST(k)))
  apply (ff.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerLeft ((boundedAboveProjectiveEquivalence k).inverse ⋙ U)
    (Functor.isoWhiskerRight (NatIso.mapHomotopyCategory e c) DerivedCategory.Qh)

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ Y, (F.obj Y).Additive]

local instance (T : Cor k) : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app T = (F.map f).app T + (F.map g).app T
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) T

local instance (P : PST(k)) : ((convolutionBifunctor F).flip.obj P).Additive where
  map_add := by
    intro X Y f g
    exact NatTrans.congr_app ((convolutionBifunctor F).map_add (f := f) (g := g)) P

/-- Integral convolution derived by the native signed projective totalization. -/
def derivedConvolution : DerivedCategory.Minus PST(k) ⥤
    DerivedCategory.Minus PST(k) ⥤ DerivedCategory.Minus PST(k) :=
  projectiveDerivedMinusBifunctor (convolutionBifunctor F)

/-- Derived convolution with a right representable is the native parameter pushforward. -/
def derivedConvolutionParameterIso (T : Cor k) :
    (derivedConvolution F).flip.obj ((singleDerivedMinus k 0).obj ((representableLarge k).obj T)) ≅
      projectiveDerivedMinusFunctor k (coendPushforward (F.flip.obj T)) :=
  projectiveDerivedMinusBifunctorSingleRightIso (convolutionBifunctor F)
      ((representableLarge k).obj T) ≪≫
    projectiveDerivedMinusFunctorIso (convolutionParameterNatIso F T)

/-- The degree-zero representable shifted by `[-n]` is the literal single in degree `n`. -/
def singleDerivedMinusShiftIso (A : PST(k)) (n : ℤ) :
    (((singleDerivedMinus k 0).obj A)⟦-n⟧) ≅ (singleDerivedMinus k n).obj A := by
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let X := (singleDerivedMinus k 0).obj A
  let e₀ := (DerivedCategory.singleFunctorIsoCompQ PST(k) 0).app A
  let eₙ := (DerivedCategory.singleFunctorIsoCompQ PST(k) n).app A
  let e := ((DerivedCategory.singleFunctors PST(k)).shiftIso (-n) n 0 (by omega)).app A
  exact V.preimageIso ((V.commShiftIso (-n)).app X ≪≫
    (shiftFunctor _ (-n)).mapIso e₀.symm ≪≫ e ≪≫ eₙ)

/-- The right parameter comparison in any single cochain degree. -/
def derivedConvolutionParameterSingleIso (T : Cor k) (n : ℤ) (K : DerivedCategory.Minus PST(k))
    [((derivedConvolution F).obj K).CommShift ℤ] :
    ((derivedConvolution F).obj K).obj
        ((singleDerivedMinus k n).obj ((representableLarge k).obj T)) ≅
      (((projectiveDerivedMinusFunctor k (coendPushforward (F.flip.obj T))).obj K)⟦-n⟧) := by
  let B := (derivedConvolution F).obj K
  let A := (representableLarge k).obj T
  exact B.mapIso (singleDerivedMinusShiftIso A n).symm ≪≫
    (B.commShiftIso (-n)).app ((singleDerivedMinus k 0).obj A) ≪≫
    (shiftFunctor _ (-n)).mapIso ((derivedConvolutionParameterIso F T).app K)

/-- The original product formula on two represented complexes in degree zero. -/
def derivedConvolutionRepresentableIso (X Y : Cor k) :
    ((derivedConvolution F).obj ((singleDerivedMinus k 0).obj ((representableLarge k).obj X))).obj
        ((singleDerivedMinus k 0).obj ((representableLarge k).obj Y)) ≅
      (singleDerivedMinus k 0).obj ((representableLarge k).obj ((F.obj X).obj Y)) :=
  (projectiveDerivedMinusBifunctorSingleRightIso (convolutionBifunctor F)
    ((representableLarge k).obj Y)).app _ ≪≫
    projectiveDerivedMinusFunctorSingleIso ((convolutionBifunctor F).flip.obj
      ((representableLarge k).obj Y)) ((representableLarge k).obj X) ≪≫
    (singleDerivedMinus k 0).mapIso (convolutionRepresentableIso F X Y)

/-- If the right slot agrees with the native parameter functor, use the original tensor. -/
def derivedConvolutionNativeParameterIso
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
    (e : F.flip.obj (Cor.mk T) ≅ Cor.parameterProduct T) :
    (derivedConvolution F).flip.obj
        ((singleDerivedMinus k 0).obj ((representableLarge k).obj (Cor.mk T))) ≅
      projectiveDerivedMinusFunctor k (parameterTensorFunctor T) := by
  refine derivedConvolutionParameterIso F (Cor.mk T) ≪≫ ?_
  apply projectiveDerivedMinusFunctorIso
  exact coendPushforwardNatIso (F.flip.obj (Cor.mk T)) e ≪≫ coendPushforwardParameterIso T

end AlgebraicGeometry.PresheafWithTransfers
