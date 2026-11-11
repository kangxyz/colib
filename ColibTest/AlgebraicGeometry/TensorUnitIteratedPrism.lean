/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitPullbackPrism

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules MonoidalCategory
open scoped Simplicial Topology unitInterval
noncomputable section
universe u
local instance tensorPrismConsumerMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

example {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory) (n : ℤ) :
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app K)).f n =
      ((MonoidalCategory.curriedTensor X.Modules).map (tensorCoefficientUnitIso X r).hom).app
        (((boundedAboveFlatPerfectPullback f).obj K).obj.X n) :=
  boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_hom_f f r K n

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) (n :
      ℤ) :
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom).app K)).f n =
      ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map ((tensorUnitPullbackNormalization
      f).inv.app K)).f n ≫
        ((MonoidalCategory.curriedTensor X.Modules).map (tensorCoefficientUnitIso X r).hom).app
          (((boundedAboveFlatPerfectPullback f).obj K).obj.X n) ≫
        ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map ((tensorUnitPullbackNormalization
      f).hom.app K)).f n :=
  tensorUnitPullbackNormalized_crossing_f f r K n

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (A : (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace)).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).obj.waldhausen.weq
      ((tensorUnitPullbackModelTransformation f r).app A) :=
  tensorUnitPullbackModelTransformation_weak f r A

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace))).obj n)
    (τ θ : (Δ[1]).obj n) :
    stageTransformationFunction (k + 1) (tensorUnitPullbackModelTransformation f r)
      (tensorUnitPullbackModelTransformation_weak f r) n
      ((stageCylinder k (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))).app
      n (A, τ)) θ =
    (stageCylinder k (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).app n
      (stageTransformationFunction k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) n A θ, τ) :=
  tensorUnitPullback_prism_structure f r k n A τ θ

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (s t : unitInterval)
    (x : Path (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))
      (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))) :
    (show Path (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
      (stagePoint 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) from
        (boundedAboveFlatPerfectTensorUnitHomotopy f r).level 0 (s, x)) t =
      stageTransformationTopHomotopy 0 (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) (s, x t) :=
  tensorUnitPullback_homotopy_zero f r s t x

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages (k + 1)).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace))).obj n)
    (τ : (Δ[1]).obj n) :
    stageTransformationFunction (k + 1) (tensorUnitPullbackModelTransformation f r)
      (tensorUnitPullbackModelTransformation_weak f r) n A τ =
    stageTransformationFunction k (rowsTransformation (tensorUnitPullbackModelTransformation f r)
      n.unop) (rowsTransformation_weak (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) n.unop) n A τ :=
  tensorUnitPullback_prism_succ f r k n A τ

