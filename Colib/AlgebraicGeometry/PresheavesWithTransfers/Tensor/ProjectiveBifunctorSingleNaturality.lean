/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingle
import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightNaturality

/-!
# Naturality in the projective single coefficient

The cochain single comparison is natural in its right coefficient.
The existing quotient and projective equivalence retain that square.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ
local notation "S(" K ")" => CochainComplex.singleFunctor PST(K) (0 : ℤ)

variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

local instance (P : PST(k)) : (F.flip.obj P).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app P = (F.map f).app P + (F.map g).app P
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) P

/-- The homotopy comparison preserves maps of degree-zero coefficients. -/
theorem signedTotalHomotopySingleRightIso_naturality {A B : PST(k)} (f : A ⟶ B)
    (K : HomotopyCategory PST(k) c) :
    (((signedTotalHomotopyBifunctor F).obj K).map
        ((HomotopyCategory.quotient PST(k) c).map ((S(k)).map f))) ≫
        (signedTotalHomotopySingleRightIso F B).hom.app K =
      (signedTotalHomotopySingleRightIso F A).hom.app K ≫
        ((F.flip.map f).mapHomotopyCategory c).app K := by
  let Q := HomotopyCategory.quotient PST(k) c
  let a := (mapBifunctorSingleRightIso F K.as A).hom
  let b := (mapBifunctorSingleRightIso F K.as B).hom
  let g := mapBifunctorMap (𝟙 K.as) ((S(k)).map f) F c
  let h := ((F.flip.map f).mapHomologicalComplex c).app K.as
  change Q.map g ≫ Q.map b = Q.map a ≫ Q.map h
  rw [← Q.map_comp, ← Q.map_comp]
  exact congrArg Q.map (mapBifunctorSingleRightIso_hom_naturality_right F K.as f)

variable [HasDerivedCategory.{w} PST(k)]

/-- The comparison on a projective model is the original homotopy map in the derived category. -/
theorem projectiveHomotopySingleRightIso_map_hom (A : PST(k)) [Projective A]
    (K : BoundedAboveProjectiveHomotopy k) :
    DerivedCategory.Minus.ι.map ((projectiveHomotopySingleRightIso F A).hom.app K) =
      DerivedCategory.Qh.map ((signedTotalHomotopySingleRightIso F A).hom.app K.obj) := by
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let Q := DerivedCategory.Qh (C := PST(k))
  let B := (projectiveHomotopyBifunctorToDerivedMinus F).flip.obj (singleProjective A 0)
  let L := projectiveHomotopyMapToDerivedMinus k (F.flip.obj A)
  let ff := (Functor.FullyFaithful.ofFullyFaithful V).whiskeringRight
    (BoundedAboveProjectiveHomotopy k)
  let t : B ⋙ V ≅ L ⋙ V := Functor.isoWhiskerLeft (boundedAboveProjectiveCondition k).ι
    (Functor.isoWhiskerRight (signedTotalHomotopySingleRightIso F A) Q)
  exact NatTrans.congr_app (ff.map_preimage (X := B) (Y := L) t.hom) K

/-- The derived comparison retains the original map in the represented parameter slot. -/
theorem projectiveDerivedMinusBifunctorSingleRightIso_naturality
    {A B : PST(k)} [Projective A] [Projective B] (f : A ⟶ B)
    (K : DerivedCategory.Minus PST(k)) :
    ((projectiveDerivedMinusBifunctor F).obj K).map ((singleDerivedMinus k 0).map f) ≫
        (projectiveDerivedMinusBifunctorSingleRightIso F B).hom.app K =
      (projectiveDerivedMinusBifunctorSingleRightIso F A).hom.app K ≫
        (projectiveDerivedMinusFunctorMap (F.flip.map f)).app K := by
  let E := boundedAboveProjectiveEquivalence k
  let H := (projectiveHomotopyBifunctorToDerivedMinus F).obj (E.inverse.obj K)
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let Q := DerivedCategory.Qh (C := PST(k))
  let K₀ := (E.inverse.obj K).obj
  let f₀ : singleProjective A 0 ⟶ singleProjective B 0 := ObjectProperty.homMk
    ((HomotopyCategory.quotient PST(k) c).map ((S(k)).map f))
  have h := congrArg H.map (singleProjectiveComparison_naturality f 0)
  rw [H.map_comp, H.map_comp] at h
  have h' := congrArg Q.map (signedTotalHomotopySingleRightIso_naturality F f K₀)
  rw [Q.map_comp, Q.map_comp] at h'
  let a := (projectiveHomotopySingleRightIso F A).hom.app (E.inverse.obj K)
  let b := (projectiveHomotopySingleRightIso F B).hom.app (E.inverse.obj K)
  let d := (projectiveDerivedMinusFunctorMap (F.flip.map f)).app K
  have hv : H.map f₀ ≫ b = a ≫ d := by
    apply V.map_injective
    rw [V.map_comp, V.map_comp]
    have ha := projectiveHomotopySingleRightIso_map_hom F A (E.inverse.obj K)
    have hb := projectiveHomotopySingleRightIso_map_hom F B (E.inverse.obj K)
    have hd := projectiveDerivedMinusFunctorMap_map_app (F.flip.map f) K
    change V.map a = _ at ha
    change V.map b = _ at hb
    change V.map d = _ at hd
    exact (congrArg (V.map (H.map f₀) ≫ ·) hb).trans
      (h'.trans ((congrArg₂ (· ≫ ·) ha hd).symm))
  change H.map (E.inverse.map ((singleDerivedMinus k 0).map f)) ≫
      (H.map (singleProjectiveComparison B 0).hom ≫ b) =
    (H.map (singleProjectiveComparison A 0).hom ≫ a) ≫ d
  rw [← Category.assoc, h, Category.assoc, hv, ← Category.assoc]

end AlgebraicGeometry.PresheafWithTransfers
