/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalOpenPairDiagram

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Generic
variable {I : Type u} [Category.{v} I]
    {A B : I ⥤ WideSubcategory preservesZero.{w}} (S : A ⟶ B)

example (i : I) : WideSubcategory preservesZero.{w} := InverseImageDiagram.model S i

example (i : I) : InverseImageDiagram.model S i ⟶ B.obj i :=
  InverseImageDiagram.component S i

example {i j : I} (f : i ⟶ j) :
    IsExact (InverseImageDiagram.model S i).obj.waldhausen.cof
      (InverseImageDiagram.model S i).obj.waldhausen.weq
      (InverseImageDiagram.model S j).obj.waldhausen.cof
      (InverseImageDiagram.model S j).obj.waldhausen.weq (A.map f).hom.toFunctor :=
  InverseImageDiagram.map_exact S f

example {i j : I} (f : i ⟶ j) :
    InverseImageDiagram.model S i ⟶ InverseImageDiagram.model S j := InverseImageDiagram.map S f

example : I ⥤ WideSubcategory preservesZero.{w} := InverseImageDiagram.diagram S

example : InverseImageDiagram.diagram S ⟶ B := InverseImageDiagram.restriction S

example : A ⟶ InverseImageDiagram.diagram S := InverseImageDiagram.changeWeak S

example : InverseImageDiagram.changeWeak S ≫ InverseImageDiagram.restriction S = S :=
  InverseImageDiagram.factor S
end Generic

example : Scheme.OpenPairs.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u+1} := pairOpenAmbient

example : pairAmbient.{u} ⟶ pairOpenAmbient := pairRestriction

example : Scheme.OpenPairs.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u+1} := pairOpen

example : pairAmbient.{u} ⟶ pairOpen := pairChangeWeak

example : pairOpen.{u} ⟶ pairOpenAmbient := pairOpenRestriction

example : pairChangeWeak.{u} ≫ pairOpenRestriction = pairRestriction := pairOpen_factor

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u+1} := ParameterModels.openModel f

example : ParameterModels.ambient Q ⟶ ParameterModels.openModel f := ParameterModels.changeWeak f

example : ParameterModels.openModel f ⟶ ParameterModels.ambient P :=
  ParameterModels.openRestriction f
