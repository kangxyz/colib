/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.WeakArrow.JointData

/-! Regression checks for genuine coherent joint data on actual opposite weak arrows. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.WeakArrow

universe u v u' v' u'' v''

section Comparison

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Type u''} [Category.{v''} T] (W : Structure D) (Wd : Structure Dᵒᵖ)
  (F : C ⥤ D) (hW : IsCompatibleDual W Wd) (L : T ⥤ Cᵒᵖ) (R : T ⥤ Dᵒᵖ)
  (τ : R ⟶ L ⋙ F.op) (hτ : ∀ t, Wd.weq (τ.app t))

example : opFunctorOfWeakComparison W Wd F hW L R τ hτ ⋙ (source W F).op = L :=
  opFunctorOfWeakComparison_source W Wd F hW L R τ hτ

example : opFunctorOfWeakComparison W Wd F hW L R τ hτ ⋙ (target W F).op = R :=
  opFunctorOfWeakComparison_target W Wd F hW L R τ hτ

example (t : T) :
    ((opFunctorOfWeakComparison W Wd F hW L R τ hτ).obj t).unop.obj.hom =
      (τ.app t).unop := rfl

example {s t : T} (f : s ⟶ t) :
    ((opFunctorOfWeakComparison W Wd F hW L R τ hτ).map f).unop.hom.left =
      (L.map f).unop := rfl

example {s t : T} (f : s ⟶ t) :
    ((opFunctorOfWeakComparison W Wd F hW L R τ hτ).map f).unop.hom.right =
      (R.map f).unop := rfl

end Comparison

section JointData

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
  (F : C ⥤ D) (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (hW : IsCompatibleDual W Wd)
  (Tc : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Vd))
  (Td : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
  (compat : Tc.joint ⋙ ExtensionCategory.postcompose Vd Wd hFd ≅ F.op.mapArrow ⋙ Td.joint)
  (hinl : ∀ f, Td.inl.app (F.op.mapArrow.obj f) ≫ (compat.inv.app f).hom.left =
    F.op.map (Tc.inl.app f))
  (hinr : ∀ f, Td.inr.app (F.op.mapArrow.obj f) ≫ (compat.inv.app f).hom.left =
    F.op.map (Tc.inr.app f))
  (hproj : ∀ f, (compat.inv.app f).hom.right ≫ F.op.map (Tc.projection.app f) =
    Td.projection.app (F.op.mapArrow.obj f))

local notation "U" => dualWaldhausenStructure V W Vd Wd F hF hFd hW
local notation "J" => jointFunctor W Wd F hW V Vd hF hFd Tc Td compat
local notation "Dc" => dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj

example : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl U) := Dc

example : (Dc).joint = J := rfl

example : J ⋙ ExtensionCategory.source U = jointSource W Wd F hW Vd hFd Tc Td compat :=
  jointFunctor_source W Wd F hW V Vd hF hFd Tc Td compat

example : J ⋙ ExtensionCategory.middle U = jointMiddle W Wd F hW Vd hFd Tc Td compat :=
  jointFunctor_middle W Wd F hW V Vd hF hFd Tc Td compat

example : J ⋙ ExtensionCategory.postcompose U Vd
    (dual_source_exact V W Vd Wd F hF hFd hW) = (source W F).op.mapArrow ⋙ Tc.joint :=
  jointFunctor_source_component W Wd F hW V Vd hF hFd Tc Td compat

example : J ⋙ ExtensionCategory.postcompose U Wd
    (dual_target_exact V W Vd Wd F hF hFd hW) = (target W F).op.mapArrow ⋙ Td.joint :=
  jointFunctor_target_component W Wd F hW V Vd hF hFd Tc Td compat

-- Cofibers are taken after exact component postcomposition. Independently chosen
-- cofibers before postcomposition are not asserted to be definitionally equal.
example : (J ⋙ ExtensionCategory.postcompose U Vd
    (dual_source_exact V W Vd Wd F hF hFd hW)) ⋙ ExtensionCategory.cofiber Vd =
      ((source W F).op.mapArrow ⋙ Tc.joint) ⋙ ExtensionCategory.cofiber Vd :=
  congrArg (fun G => G ⋙ ExtensionCategory.cofiber Vd)
    (jointFunctor_source_component W Wd F hW V Vd hF hFd Tc Td compat)

example : (J ⋙ ExtensionCategory.postcompose U Wd
    (dual_target_exact V W Vd Wd F hF hFd hW)) ⋙ ExtensionCategory.cofiber Wd =
      ((target W F).op.mapArrow ⋙ Td.joint) ⋙ ExtensionCategory.cofiber Wd :=
  congrArg (fun G => G ⋙ ExtensionCategory.cofiber Wd)
    (jointFunctor_target_component W Wd F hW V Vd hF hFd Tc Td compat)

example : IsExact (ArrowCategory.waldhausenStructure U).cof
    (ArrowCategory.waldhausenStructure U).weq
    (ExtensionCategory.waldhausenStructure U).cof
    (ExtensionCategory.waldhausenStructure U).weq J :=
  jointFunctor_exact V W Vd Wd F hF hFd hW Tc Td compat

example (f : Arrow (Obj W F)ᵒᵖ) : (U).cof ((J).obj f).obj.hom := ((J).obj f).property

example (f : Arrow (Obj W F)ᵒᵖ) :
    (source W F).op.map ((J).obj f).obj.hom =
      (Tc.joint.obj ((source W F).op.mapArrow.obj f)).obj.hom := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (target W F).op.map ((J).obj f).obj.hom =
      (Td.joint.obj ((target W F).op.mapArrow.obj f)).obj.hom := rfl

example {f g : Arrow (Obj W F)ᵒᵖ} (α : f ⟶ g) :
    (source W F).op.map ((J).map α).hom.left =
      (Tc.joint.map ((source W F).op.mapArrow.map α)).hom.left := rfl

example {f g : Arrow (Obj W F)ᵒᵖ} (α : f ⟶ g) :
    (source W F).op.map ((J).map α).hom.right =
      (Tc.joint.map ((source W F).op.mapArrow.map α)).hom.right := rfl

example {f g : Arrow (Obj W F)ᵒᵖ} (α : f ⟶ g) :
    (target W F).op.map ((J).map α).hom.left =
      (Td.joint.map ((target W F).op.mapArrow.map α)).hom.left := rfl

example {f g : Arrow (Obj W F)ᵒᵖ} (α : f ⟶ g) :
    (target W F).op.map ((J).map α).hom.right =
      (Td.joint.map ((target W F).op.mapArrow.map α)).hom.right := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (Dc).inl.app f ≫ ((Dc).joint.obj f).obj.hom ≫ (Dc).projection.app f = f.hom :=
  (Dc).factorization f

example (f : Arrow (Obj W F)ᵒᵖ) : (U).weq ((Dc).projection.app f) := (Dc).weak f

example (f : Arrow (Obj W F)ᵒᵖ) :
    IsColimit (BinaryCofan.mk ((Dc).inl.app f) ((Dc).inr.app f)) := (Dc).coproduct f

example (f : Arrow (Obj W F)ᵒᵖ) :
    (Dc).inl.app f = (jointInl W F Wd hW Vd hFd Tc Td compat hinl).app f := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (Dc).inr.app f = (jointInr W F Wd hW Vd hFd Tc Td compat hinr).app f := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (Dc).projection.app f =
      (jointProjection W F Wd hW Vd hFd Tc Td compat hproj).app f := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (source W F).op.map ((Dc).inl.app f) =
      (Tc.inl.app ((source W F).op.mapArrow.obj f)) := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (target W F).op.map ((Dc).inl.app f) =
      (Td.inl.app ((target W F).op.mapArrow.obj f)) := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (source W F).op.map ((Dc).inr.app f) =
      (Tc.inr.app ((source W F).op.mapArrow.obj f)) := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (target W F).op.map ((Dc).inr.app f) =
      (Td.inr.app ((target W F).op.mapArrow.obj f)) := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (source W F).op.map ((Dc).projection.app f) =
      (Tc.projection.app ((source W F).op.mapArrow.obj f)) := rfl

example (f : Arrow (Obj W F)ᵒᵖ) :
    (target W F).op.map ((Dc).projection.app f) =
      (Td.projection.app ((target W F).op.mapArrow.obj f)) := rfl

end JointData
