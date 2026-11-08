/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.WeakArrow.JointFunctor

/-!
# Original endpoints and projection of the weak-arrow joint functor

The three explicit compatibility equations for the actual component
inclusions and projection construct genuine natural endpoint maps and a
weak projection in the original opposite weak-arrow category. The original
factorization equation holds literally. Every component formula is
retained by an rfl lemma. No endpoint compatibility is inferred from an
arbitrary natural isomorphism.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/JointEndpoints.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original hypotheses, functors, component maps and independent universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
namespace CategoryTheory.Waldhausen.WeakArrow
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure D) (F : C ⥤ D)

/-- Construct an original opposite weak-arrow morphism from its actual
components and the original reversed commuting square. -/
def opHomMk {X Y : (Obj W F)ᵒᵖ}
    (l : (source W F).op.obj X ⟶ (source W F).op.obj Y)
    (r : (target W F).op.obj X ⟶ (target W F).op.obj Y)
    (w : r ≫ Y.unop.obj.hom.op = X.unop.obj.hom.op ≫ F.op.map l) : X ⟶ Y :=
  ((objects W F).homMk (show Y.unop.obj ⟶ X.unop.obj from
    ⟨l.unop, r.unop, (congrArg Quiver.Hom.unop w).symm⟩)).op

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem opHomMk_unop_source {X Y : (Obj W F)ᵒᵖ}
    (l : (source W F).op.obj X ⟶ (source W F).op.obj Y)
    (r : (target W F).op.obj X ⟶ (target W F).op.obj Y)
    (w : r ≫ Y.unop.obj.hom.op = X.unop.obj.hom.op ≫ F.op.map l) :
    (source W F).map (opHomMk W F l r w).unop = (l).unop := rfl

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem opHomMk_unop_target {X Y : (Obj W F)ᵒᵖ}
    (l : (source W F).op.obj X ⟶ (source W F).op.obj Y)
    (r : (target W F).op.obj X ⟶ (target W F).op.obj Y)
    (w : r ≫ Y.unop.obj.hom.op = X.unop.obj.hom.op ≫ F.op.map l) :
    (target W F).map (opHomMk W F l r w).unop = (r).unop := rfl

lemma op_hom_ext {X Y : (Obj W F)ᵒᵖ} (f g : X ⟶ Y)
    (hl : (source W F).op.map f = (source W F).op.map g)
    (hr : (target W F).op.map f = (target W F).op.map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · exact congrArg Quiver.Hom.unop hl
  · exact congrArg Quiver.Hom.unop hr

variable (Wd : Structure Dᵒᵖ) (hW : IsCompatibleDual W Wd)
  (V : Structure C) (Vd : Structure Cᵒᵖ)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (Tc : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Vd))
  (Td : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
  (compat : Tc.joint ⋙ ExtensionCategory.postcompose Vd Wd hFd ≅ F.op.mapArrow ⋙ Td.joint)
  (hinl : ∀ f, Td.inl.app (F.op.mapArrow.obj f) ≫ (compat.inv.app f).hom.left =
    F.op.map (Tc.inl.app f))
  (hinr : ∀ f, Td.inr.app (F.op.mapArrow.obj f) ≫ (compat.inv.app f).hom.left =
    F.op.map (Tc.inr.app f))
  (hproj : ∀ f, (compat.inv.app f).hom.right ≫ F.op.map (Tc.projection.app f) =
    Td.projection.app (F.op.mapArrow.obj f))

/-- The first endpoint is an actual natural arrow in the original opposite
weak-arrow category, using the honest compatibility equation for inl. -/
def jointInl : Arrow.leftFunc ⟶ jointSource W Wd F hW Vd hFd Tc Td compat where
  app f := opHomMk W F (Tc.inl.app ((source W F).op.mapArrow.obj f))
    (Td.inl.app ((target W F).op.mapArrow.obj f)) (by
      change Td.inl.app _ ≫ ((Td.joint.map ((reversedArrowComparison W F).app f)).hom.left ≫
        (compat.inv.app _).hom.left) = _
      have hn := Td.inl.naturality ((reversedArrowComparison W F).app f)
      change _ ≫ Td.inl.app _ = Td.inl.app _ ≫
        (Td.joint.map ((reversedArrowComparison W F).app f)).hom.left at hn
      rw [← Category.assoc, ← hn, Category.assoc]
      exact congrArg (fun k => f.left.unop.obj.hom.op ≫ k)
        (hinl ((source W F).op.mapArrow.obj f)))
  naturality {f g} α := by
    apply op_hom_ext W F
    · exact Tc.inl.naturality ((source W F).op.mapArrow.map α)
    · exact Td.inl.naturality ((target W F).op.mapArrow.map α)

/-- The second original endpoint, with actual component maps retained. -/
def jointInr : Arrow.rightFunc ⟶ jointSource W Wd F hW Vd hFd Tc Td compat where
  app f := opHomMk W F (Tc.inr.app ((source W F).op.mapArrow.obj f))
    (Td.inr.app ((target W F).op.mapArrow.obj f)) (by
      change Td.inr.app _ ≫ ((Td.joint.map ((reversedArrowComparison W F).app f)).hom.left ≫
        (compat.inv.app _).hom.left) = _
      have hn := Td.inr.naturality ((reversedArrowComparison W F).app f)
      change _ ≫ Td.inr.app _ = Td.inr.app _ ≫
        (Td.joint.map ((reversedArrowComparison W F).app f)).hom.left at hn
      rw [← Category.assoc, ← hn, Category.assoc]
      exact congrArg (fun k => f.right.unop.obj.hom.op ≫ k)
        (hinr ((source W F).op.mapArrow.obj f)))
  naturality {f g} α := by
    apply op_hom_ext W F
    · exact Tc.inr.naturality ((source W F).op.mapArrow.map α)
    · exact Td.inr.naturality ((target W F).op.mapArrow.map α)

/-- The actual weak projection uses the honest component projection
compatibility, with literal maps into the original right endpoint. -/
def jointProjection : jointMiddle W Wd F hW Vd hFd Tc Td compat ⟶ Arrow.rightFunc where
  app f := opHomMk W F (Tc.projection.app ((source W F).op.mapArrow.obj f))
    (Td.projection.app ((target W F).op.mapArrow.obj f)) (by
      change _ = ((Td.joint.map ((reversedArrowComparison W F).app f)).hom.right ≫
        (compat.inv.app _).hom.right) ≫ F.op.map
          (Tc.projection.app ((source W F).op.mapArrow.obj f))
      rw [Category.assoc, hproj]
      exact (Td.projection.naturality ((reversedArrowComparison W F).app f)).symm)
  naturality {f g} α := by
    apply op_hom_ext W F
    · exact Tc.projection.naturality ((source W F).op.mapArrow.map α)
    · exact Td.projection.naturality ((target W F).op.mapArrow.map α)

/-- The original input arrow is retained in the exact factorization equation. -/
lemma joint_factorization (f : Arrow (Obj W F)ᵒᵖ) :
    (jointInl W F Wd hW Vd hFd Tc Td compat hinl).app f ≫
      (jointInclusion W Wd F hW Vd hFd Tc Td compat).app f ≫
      (jointProjection W F Wd hW Vd hFd Tc Td compat hproj).app f = f.hom := by
  apply op_hom_ext W F
  · exact Tc.factorization ((source W F).op.mapArrow.obj f)
  · exact Td.factorization ((target W F).op.mapArrow.obj f)

/-- The actual projection is weak in the genuine opposite weak-arrow structure. -/
lemma jointProjection_weak (f : Arrow (Obj W F)ᵒᵖ) :
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).weq
      ((jointProjection W F Wd hW Vd hFd Tc Td compat hproj).app f) :=
  ⟨Tc.weak ((source W F).op.mapArrow.obj f), Td.weak ((target W F).op.mapArrow.obj f)⟩

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem jointInl_unop_source (f : Arrow (Obj W F)ᵒᵖ) :
    (source W F).map
      ((jointInl W F Wd hW Vd hFd Tc Td compat hinl).app f).unop = (Tc.inl.app ((source W
          F).op.mapArrow.obj f)).unop := rfl

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem jointInl_unop_target (f : Arrow (Obj W F)ᵒᵖ) :
    (target W F).map
      ((jointInl W F Wd hW Vd hFd Tc Td compat hinl).app f).unop = (Td.inl.app ((target W
          F).op.mapArrow.obj f)).unop := rfl

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem jointInr_unop_source (f : Arrow (Obj W F)ᵒᵖ) :
    (source W F).map
      ((jointInr W F Wd hW Vd hFd Tc Td compat hinr).app f).unop = (Tc.inr.app ((source W
          F).op.mapArrow.obj f)).unop := rfl

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem jointInr_unop_target (f : Arrow (Obj W F)ᵒᵖ) :
    (target W F).map
      ((jointInr W F Wd hW Vd hFd Tc Td compat hinr).app f).unop = (Td.inr.app ((target W
          F).op.mapArrow.obj f)).unop := rfl

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem jointProjection_unop_source (f : Arrow (Obj W F)ᵒᵖ) :
    (source W F).map
      ((jointProjection W F Wd hW Vd hFd Tc Td compat hproj).app f).unop = (Tc.projection.app
          ((source W F).op.mapArrow.obj f)).unop := rfl

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem jointProjection_unop_target (f : Arrow (Obj W F)ᵒᵖ) :
    (target W F).map
      ((jointProjection W F Wd hW Vd hFd Tc Td compat hproj).app f).unop = (Td.projection.app
          ((target W F).op.mapArrow.obj f)).unop := rfl

end CategoryTheory.Waldhausen.WeakArrow
