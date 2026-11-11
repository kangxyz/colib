/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientRealization
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
  CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
noncomputable section

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq).obj n) (τ θ : (Δ[1]).obj n) :
    tensorUnitPullbackCoefficientSimplex f r n A τ θ =
      (suspensionCylinder (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).app n
        ((tensorUnitPullbackNormalizedCylinder f r).app n (A, τ), θ) :=
  tensorUnitPullbackCoefficientSimplex_eq f r n A τ θ

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackCoefficientCylinder f r =
      (tensorUnitPullbackNormalizedCylinder f r ▷ Δ[1]) ≫
        suspensionCylinder (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) :=
  tensorUnitPullbackCoefficientCylinder_eq f r

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (s t : unitInterval)
    (x : (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).Delooping) :
    tensorUnitPullbackCoefficientRealization f r (s, (t, x)) =
      loopStructureMap (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        (weakNaturalTransformationRealizationHomotopy
          (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace)
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
          (normalizedWeakTransformation_weak (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
            (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _
      inferInstance)) (t, x)) s :=
  tensorUnitPullbackCoefficientRealization_eq f r s t x

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (t : unitInterval)
    (x : (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).Delooping) :
    (boundedAboveFlatPerfectTensorUnitHomotopy f r).level 1
        (t, (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).asSmallDeloopingHomeomorph x) =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmallDeloopingHomeomorph
        (weakNaturalTransformationRealizationHomotopy
          (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace)
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
          (normalizedWeakTransformation_weak (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
            (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _
      inferInstance)) (t, x)) :=
  tensorUnitPullbackNormalizedRealization_track f r t x

