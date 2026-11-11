/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterOpenTrack

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentUnit
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass KTheory.Bass.NaturalTrack
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example (X : Scheme.{u}ᵒᵖ) :
    𝟭 ((ParameterModels.openModel f).obj (laurent.op.obj X)).obj.Obj ≅
    𝟭 ((ParameterModels.openModel f).obj (laurent.op.obj X)).obj.Obj := openUnit f X

example {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.openModel f).map (laurent.op.map g)).hom.toFunctor
      (openUnit f X) (openUnit f Y) := openUnit_naturality f g

example : Track laurent.op coefficient (ParameterModels.openModel f ⋙ prespectrumFunctor) :=
  openTrack f

example (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.changeWeak f).app (laurent.op.obj X)).hom.toFunctor
      (ambientUnit Q X) (openUnit f X) := changeWeak_unit f X

example (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.openRestriction f).app (laurent.op.obj X)).hom.toFunctor
      (openUnit f X) (ambientUnit P X) := openRestriction_unit f X

example : Equivariant (ambientTrack Q) (openTrack f)
    (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor) :=
  changeWeak_equivariant f

example : Equivariant (openTrack f) (ambientTrack P)
    (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor) :=
  openRestriction_equivariant f
