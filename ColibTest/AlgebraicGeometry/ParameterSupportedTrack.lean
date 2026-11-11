/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterSupportedTrack

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentUnit
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass KTheory.Bass.NaturalTrack
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example : Track laurent.op coefficient (ParameterModels.ambient Q ⋙ prespectrumFunctor) :=
  ambientTrack Q

example (X : Scheme.{u}ᵒᵖ) :
    ObjectProperty ((ParameterModels.ambient Q).obj X).obj.Obj := parameterSupported f X

example (X : Scheme.{u}ᵒᵖ) :
    𝟭 (parameterSupported f (laurent.op.obj X)).FullSubcategory ≅
    𝟭 (parameterSupported f (laurent.op.obj X)).FullSubcategory := supportedUnit f X

example {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.supported f).map (laurent.op.map g)).hom.toFunctor
      (supportedUnit f X) (supportedUnit f Y) := supportedUnit_naturality f g

example : Track laurent.op coefficient (ParameterModels.supported f ⋙ prespectrumFunctor) :=
  supportedTrack f

example (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.forget f).app (laurent.op.obj X)).hom.toFunctor
      (supportedUnit f X) (ambientUnit Q X) := forget_unit f X

example : Equivariant (supportedTrack f) (ambientTrack Q)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) :=
  forget_equivariant f
