/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterLaurentUnit

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentUnit
open CategoryTheory.Functor.IdentityAutomorphism

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

example (X : Scheme.{u}ᵒᵖ) : (Γ((laurent.op.obj X).unop, ⊤))ˣ := laurentScalar X

example {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Units.map (laurent.op.map g).unop.appTop.hom.toMonoidHom (laurentScalar X) =
      laurentScalar Y := laurentScalar_map g

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (Γ(((baseProductFunctor (specULiftZIsTerminal.from Q)).op.obj
      (laurent.op.obj X)).unop, ⊤))ˣ := projectedLaurentScalar Q X

example (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Units.map (((baseProductFunctor (specULiftZIsTerminal.from Q)).op.map
      (laurent.op.map g)).unop).appTop.hom.toMonoidHom (projectedLaurentScalar Q X) =
      projectedLaurentScalar Q Y := projectedLaurentScalar_map Q g

example {P Q : Scheme.{u}} (f : P ⟶ Q) (X : Scheme.{u}ᵒᵖ) :
    Units.map ((baseProductTransformation (specULiftZIsTerminal.from P)
      (specULiftZIsTerminal.from Q) f (specULiftZIsTerminal.hom_ext _ _)).app
      (laurent.op.obj X).unop).appTop.hom.toMonoidHom (projectedLaurentScalar Q X) =
      projectedLaurentScalar P X := projectedLaurentScalar_factor f X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    𝟭 (BoundedAboveFlatGlobalSections ((baseProductFunctor
      (specULiftZIsTerminal.from Q)).op.obj (laurent.op.obj X))) ≅
    𝟭 (BoundedAboveFlatGlobalSections ((baseProductFunctor
      (specULiftZIsTerminal.from Q)).op.obj (laurent.op.obj X))) := ambientUnit Q X

example (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves (boundedAboveFlatGlobalSectionsMap
      ((baseProductFunctor (specULiftZIsTerminal.from Q)).op.map (laurent.op.map g)))
      (ambientUnit Q X) (ambientUnit Q Y) := ambientUnit_naturality Q g

example {P Q : Scheme.{u}} (f : P ⟶ Q) (X : Scheme.{u}ᵒᵖ) :
    Preserves (boundedAboveFlatGlobalSectionsMap
      (((baseProductTransformation (specULiftZIsTerminal.from P)
        (specULiftZIsTerminal.from Q) f (specULiftZIsTerminal.hom_ext _ _)).app
        (laurent.op.obj X).unop).op)) (ambientUnit Q X) (ambientUnit P X) :=
  ambientUnit_factor f X
