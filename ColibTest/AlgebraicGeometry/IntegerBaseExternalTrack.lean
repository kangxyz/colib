/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseExternalTrack
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v w
namespace AlgebraicGeometry.Scheme.Products
variable {S T U : Scheme.{u}}
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductFunctor r).map (baseProductSwapMap p q X) ≫
        baseProductSwapMap p r ((baseProductFunctor q).obj X) ≫
          (baseProductFunctor p).map (baseProductSwapMap q r X) =
      baseProductSwapMap q r ((baseProductFunctor p).obj X) ≫
        (baseProductFunctor q).map (baseProductSwapMap p r X) ≫
          baseProductSwapMap p q ((baseProductFunctor r).obj X) :=
  baseProductSwapMap_braid p q r X

example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductFunctor r).map (baseProductSwapMap p q X) ≫
        baseProductMoveExternal q p r X =
      baseProductMoveExternal p q r X ≫
        baseProductSwapMap p q ((baseProductFunctor r).obj X) :=
  baseProductMoveExternal_swap p q r X

example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductMoveExternal q p r X).op ≫
        ((baseProductFunctor r).map (baseProductSwapMap p q X)).op =
      (baseProductSwapMap p q ((baseProductFunctor r).obj X)).op ≫
        (baseProductMoveExternal p q r X).op :=
  baseProductMoveExternal_swap_op p q r X

example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    baseProductMoveExternal p q r X ≫
        pullback.fst
          (specULiftZIsTerminal.from ((baseProductFunctor p).obj
            ((baseProductFunctor r).obj X))) q ≫
          pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor r).obj X)) p ≫
            pullback.snd (specULiftZIsTerminal.from X) r =
      pullback.snd
        (specULiftZIsTerminal.from
          ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))) r :=
  baseProductMoveExternal_projection p q r X

example {C : Type v} [Category.{w} C]
    (F : Scheme.{u}ᵒᵖ ⥤ C) (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (τ : F ⟶ (baseProductFunctor r).op ⋙ F) (X : Scheme.{u}) :
    F.map (baseProductSwapMap p q X).op ≫ baseProductExternalTrack F p q r τ X =
      baseProductExternalTrack F q p r τ X ≫
        F.map (baseProductSwapMap p q ((baseProductFunctor r).obj X)).op :=
  baseProductExternalTrack_swap F p q r τ X

end AlgebraicGeometry.Scheme.Products
end
