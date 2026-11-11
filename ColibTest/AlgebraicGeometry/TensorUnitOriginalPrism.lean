/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitNervePrism

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Functor
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
open scoped Simplicial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

example (X : Scheme.{u}) :
    IsExact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectTensorUnit X) := boundedAboveFlatPerfectTensorUnit_exact X

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    Homotopy (boundedAboveFlatPerfectTensorUnitPrespectrumMap f)
      (boundedAboveFlatPerfectTensorUnitPrespectrumMap f) :=
  boundedAboveFlatPerfectTensorUnitHomotopy f r

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedAboveFlatPerfectTensorUnitPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  boundedAboveFlatPerfectTensorUnitUnitorHomotopy f

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    ((boundedAboveFlatPerfectTensorUnitHomotopy f r).trans
      (boundedAboveFlatPerfectTensorUnitUnitorHomotopy f)).RelHomotopy
      ((boundedAboveFlatPerfectTensorUnitUnitorHomotopy f).trans
        (boundedAboveFlatPerfectUnitHomotopy f r)) :=
  boundedAboveFlatPerfectTensorUnitUnitorPasting f r

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ CochainComplex X.Modules ℤ) (τ : m ⟶ ⦋1⦌) :
    complexTensorUnitPrism X r A τ =
      nerveCylinderDiagram (whiskerLeft A (complexTensorUnitAutomorphism X r).hom) τ :=
  complexTensorUnitPrism_eq_nerve X r A τ

example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (whiskerLeft A (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom) τ ⋙
      (boundedAboveFlatPerfectComplex X.toRingedSpace).ι =
    complexTensorUnitPrism X r (A ⋙ (boundedAboveFlatPerfectComplex X.toRingedSpace).ι) τ :=
  boundedAboveFlatPerfectTensorUnitPrism_original X r A τ
