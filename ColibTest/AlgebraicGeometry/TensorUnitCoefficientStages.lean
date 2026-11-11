/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientStages
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
  CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u v
noncomputable section

example {C : Type u} [Category.{v} C] (W : Structure C) :
    (W.asSmallSSetIso.hom ▷ Δ[1]) ≫ suspensionCylinder W.asSmall =
      suspensionCylinder W ≫ W.asSmallDoubleDiagonalMap :=
  W.asSmall_suspensionCylinder

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackSmallCoefficientCylinder f r =
      (stageTransformationCylinder 0 (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) ▷ Δ[1]) ≫
        stageCylinder 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  tensorUnitPullbackSmallCoefficientCylinder_eq f r

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (k : ℕ) :
    tensorUnitPullbackCoefficientStageCylinder f r k =
      (stageTransformationCylinder k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) ▷ Δ[1]) ≫
        stageCylinder k (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  tensorUnitPullbackCoefficientStageCylinder_eq f r k

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackCoefficientStageCylinder f r 0 =
      tensorUnitPullbackSmallCoefficientCylinder f r :=
  tensorUnitPullbackCoefficientStageCylinder_zero f r

