/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedConvolution
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingleNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardParameterMap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveCoefficientMap

/-!
# Maps of represented parameters

A map of parameters acts by postcomposition on the actual correspondence
factor. This is the left-adjoint mate of precomposition on the parameter
sections. The comparison with convolution retains that action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ X, (F.obj X).Additive]

local instance (T : Cor k) : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app T = (F.map f).app T + (F.map g).app T
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) T

/-- The convolution parameter comparison preserves the map of represented parameters. -/
theorem convolutionParameterNatIso_naturality_right {T T' : Cor k} (f : T ⟶ T') (P : PST(k)) :
    convolutionMap F (𝟙 P) ((representableLarge k).map f) ≫ (convolutionParameterIso F T' P).hom =
      (convolutionParameterIso F T P).hom ≫
        (coendPushforwardParameterMap (F.flip.map f)).app P := by
  apply convolutionPresheaf_hom_ext
  rintro U Y Z s ⟨b⟩ a
  change (convolutionParameterIso F T' P).hom.hom.app (op U)
      ((convolutionMap F (𝟙 P) ((representableLarge k).map f)).hom.app (op U)
        (convolutionGenerator F P ((representableLarge k).obj T) U Y Z s (ULift.up b) a)) =
    ((coendPushforwardParameterMap (F.flip.map f)).app P).hom.app (op U)
      ((convolutionParameterIso F T P).hom.hom.app (op U)
        (convolutionGenerator F P ((representableLarge k).obj T) U Y Z s (ULift.up b) a))
  rw [convolutionMap_generator, representableLarge_map_app_apply,
    convolutionParameterIso_hom_generator, convolutionParameterIso_hom_generator,
    coendPushforwardParameterMap_generator, Functor.map_comp, Category.assoc]
  rfl

variable [HasDerivedCategory.{w} (PST(k))]

private theorem projectiveCoefficientComparison_naturality
    {A B A' B' : PST(k) ⥤ PST(k)}
    [A.Additive] [B.Additive] [A'.Additive] [B'.Additive]
    (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (eq : f ≫ e'.hom = e.hom ≫ g) (K : DerivedCategory.Minus PST(k)) :
    (projectiveDerivedMinusFunctorMap f).app K ≫
      (projectiveDerivedMinusFunctorIso e').hom.app K =
      (projectiveDerivedMinusFunctorIso e).hom.app K ≫
        (projectiveDerivedMinusFunctorMap g).app K := by
  let I := (boundedAboveProjectiveEquivalence k).inverse ⋙
    (boundedAboveProjectiveCondition k).ι
  let Q := DerivedCategory.Qh (C := PST(k))
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let c := ComplexShape.up ℤ
  let ff := (Functor.FullyFaithful.ofFullyFaithful V).whiskeringRight (DerivedCategory.Minus PST(k))
  apply V.map_injective
  rw [V.map_comp, V.map_comp, projectiveDerivedMinusFunctorMap_map_app,
    projectiveDerivedMinusFunctorMap_map_app]
  have h₁ := NatTrans.congr_app (ff.map_preimage
    (X := projectiveDerivedMinusFunctor k A') (Y := projectiveDerivedMinusFunctor k B')
    (Functor.whiskerLeft I (Functor.whiskerRight (NatIso.mapHomotopyCategory e' c).hom Q))) K
  have h₂ := NatTrans.congr_app (ff.map_preimage
    (X := projectiveDerivedMinusFunctor k A) (Y := projectiveDerivedMinusFunctor k B)
    (Functor.whiskerLeft I (Functor.whiskerRight (NatIso.mapHomotopyCategory e c).hom Q))) K
  change V.map ((projectiveDerivedMinusFunctorIso e').hom.app K) = _ at h₁
  change V.map ((projectiveDerivedMinusFunctorIso e).hom.app K) = _ at h₂
  rw [h₁, h₂]
  change Q.map ((f.mapHomotopyCategory c).app (I.obj K)) ≫
      Q.map ((e'.hom.mapHomotopyCategory c).app (I.obj K)) =
    Q.map ((e.hom.mapHomotopyCategory c).app (I.obj K)) ≫
      Q.map ((g.mapHomotopyCategory c).app (I.obj K))
  rw [← Q.map_comp, ← Q.map_comp]
  apply congrArg Q.map
  have h := congrArg (fun t => t.mapHomotopyCategory c) eq
  rw [NatTrans.mapHomotopyCategory_comp, NatTrans.mapHomotopyCategory_comp] at h
  exact NatTrans.congr_app h (I.obj K)

private theorem projectiveSingleParameterComparison_naturality
    (C : PST(k) ⥤ PST(k) ⥤ PST(k)) [C.Additive] [∀ X, (C.obj X).Additive]
    {X Y : PST(k)} [Projective X] [Projective Y] (f : X ⟶ Y)
    {A B : PST(k) ⥤ PST(k)} [A.Additive] [B.Additive]
    [((C.flip).obj X).Additive] [((C.flip).obj Y).Additive]
    (e : C.flip.obj X ≅ A) (d : C.flip.obj Y ≅ B)
    (g : A ⟶ B) (h : C.flip.map f ≫ d.hom = e.hom ≫ g)
    (K : DerivedCategory.Minus PST(k)) :
    ((projectiveDerivedMinusBifunctor C).obj K).map ((singleDerivedMinus k 0).map f) ≫
      ((projectiveDerivedMinusBifunctorSingleRightIso C Y ≪≫
        projectiveDerivedMinusFunctorIso d).hom.app K) =
    (projectiveDerivedMinusBifunctorSingleRightIso C X ≪≫
      projectiveDerivedMinusFunctorIso e).hom.app K ≫
        (projectiveDerivedMinusFunctorMap g).app K := by
  let α := projectiveDerivedMinusBifunctorSingleRightIso C X
  let β := projectiveDerivedMinusBifunctorSingleRightIso C Y
  let d₀ := projectiveDerivedMinusFunctorIso d
  let e₀ := projectiveDerivedMinusFunctorIso e
  have h₁ := projectiveDerivedMinusBifunctorSingleRightIso_naturality C f K
  have h₂ := projectiveCoefficientComparison_naturality e d (C.flip.map f) g h K
  change ((projectiveDerivedMinusBifunctor C).obj K).map ((singleDerivedMinus k 0).map f) ≫
      (β.hom.app K ≫ d₀.hom.app K) =
    (α.hom.app K ≫ e₀.hom.app K) ≫ (projectiveDerivedMinusFunctorMap g).app K
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ d₀.hom.app K) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (α.hom.app K ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- The signed derived parameter comparison retains the original maps of correspondences. -/
theorem derivedConvolutionParameterIso_naturality_right {T T' : Cor k} (f : T ⟶ T')
    (K : DerivedCategory.Minus PST(k)) :
    ((derivedConvolution F).obj K).map ((singleDerivedMinus k 0).map
        ((representableLarge k).map f)) ≫ (derivedConvolutionParameterIso F T').hom.app K =
      (derivedConvolutionParameterIso F T).hom.app K ≫
        (projectiveDerivedMinusFunctorMap (coendPushforwardParameterMap (F.flip.map f))).app K := by
  let C := convolutionBifunctor F
  let f₀ := (representableLarge k).map f
  let t := coendPushforwardParameterMap (F.flip.map f)
  let e := convolutionParameterNatIso F T
  let e' := convolutionParameterNatIso F T'
  have h : C.flip.map f₀ ≫ e'.hom = e.hom ≫ t := by
    apply NatTrans.ext
    funext P
    exact convolutionParameterNatIso_naturality_right F f P
  exact projectiveSingleParameterComparison_naturality C f₀ e e' t h K

end AlgebraicGeometry.PresheafWithTransfers
