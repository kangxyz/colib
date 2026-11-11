/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationUnit

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
noncomputable section
open Topology.LoopPrespectrum
universe u v u₁ v₁

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) ⟶ asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) :=
  evaluationRawMap f

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (Opposite.op X)) ⋙ AsSmall.up ≅
      evaluationSmall (Opposite.op Y) ⋙ (evaluationRawMap f).hom.toFunctor :=
  evaluationMiddleIso f

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatGlobalSectionModelFunctor.map f.op ≫ evaluationModel (Opposite.op
      X)).hom.toFunctor ≅
      (evaluationModel (Opposite.op Y) ≫ evaluationRawMap f).hom.toFunctor :=
  evaluationComparisonIso f

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy
      (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map f.op) ≫ prespectrumMap
      (evaluationModel (Opposite.op X)))
      (prespectrumMap (evaluationModel (Opposite.op Y)) ≫ prespectrumMap (evaluationRawMap f)) :=
  evaluationComparison f

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    (evaluationRawMap f).hom.toFunctor ⟶
      (evaluationRawMap f).hom.toFunctor :=
  evaluationRawUnit f r

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    evaluationRawUnit f r =
      (onFunctor (evaluationRawMap f).hom.toFunctor
        (evaluationSmallUnit (Opposite.op X) r)).hom :=
  evaluationRawUnit_eq f r

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    whiskerRight (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
        (boundedAboveFlatGlobalSectionUnit (Opposite.op X) r)).hom (evaluationModel (Opposite.op
      X)).hom.toFunctor ≫
      (evaluationComparisonIso f).hom =
    (evaluationComparisonIso f).hom ≫
      whiskerLeft (evaluationModel (Opposite.op Y)).hom.toFunctor (evaluationRawUnit f r) :=
  evaluation_unit_square f r

