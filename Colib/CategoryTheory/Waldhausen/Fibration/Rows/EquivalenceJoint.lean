/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ArrowCategory.Exact
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ReflexiveFactorization
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Transport of actual joint-cylinder data along exact equivalences

Both directions are genuine exact functors. Endpoint arrows are transported
using the original counit, and the coproduct and factorization identities
retain these specified arrows.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Fibration/Rows/EquivalenceJoint.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
namespace Fibration.RowFactorization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (e : C ≌ D)
  (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)
  (T : JointData (NestedWeakEquivalences.refl V))

/-- The actual joint functor is transported, with its original endpoint arrows. -/
def equivalenceJoint := e.inverse.mapArrow ⋙ T.joint ⋙ ExtensionCategory.postcompose V W hF

/-- The natural map from an arrow source to the transported joint source, obtained from the
first endpoint map of `T` and the inverse counit of `e`. -/
def equivalenceInl : Arrow.leftFunc ⟶ equivalenceJoint V W e hF T ⋙ ExtensionCategory.source W where
  app f := (e.counitIso.app f.left).inv ≫ e.functor.map (T.inl.app (e.inverse.mapArrow.obj f))
  naturality {f g} α := by
    have he : α.left ≫ (e.counitIso.app g.left).inv =
        (e.counitIso.app f.left).inv ≫ e.functor.map (e.inverse.map α.left) :=
      e.counitIso.inv.naturality α.left
    have ht := congrArg e.functor.map (T.inl.naturality (e.inverse.mapArrow.map α))
    simp only [Functor.map_comp] at ht
    change e.functor.map (e.inverse.map α.left) ≫ e.functor.map (T.inl.app
      (e.inverse.mapArrow.obj g)) =
      e.functor.map (T.inl.app (e.inverse.mapArrow.obj f)) ≫
        e.functor.map ((T.joint.map (e.inverse.mapArrow.map α)).hom.left) at ht
    change α.left ≫ ((e.counitIso.app g.left).inv ≫ _) =
      ((e.counitIso.app f.left).inv ≫ _) ≫ e.functor.map _
    rw [← Category.assoc, he, Category.assoc, ht, ← Category.assoc]

/-- The natural map from an arrow target to the transported joint source, obtained from the
second endpoint map of `T` and the inverse counit of `e`. -/
def equivalenceInr : Arrow.rightFunc ⟶ equivalenceJoint V W e hF T ⋙ ExtensionCategory.source W
    where
  app f := (e.counitIso.app f.right).inv ≫ e.functor.map (T.inr.app (e.inverse.mapArrow.obj f))
  naturality {f g} α := by
    have he : α.right ≫ (e.counitIso.app g.right).inv =
        (e.counitIso.app f.right).inv ≫ e.functor.map (e.inverse.map α.right) :=
      e.counitIso.inv.naturality α.right
    have ht := congrArg e.functor.map (T.inr.naturality (e.inverse.mapArrow.map α))
    simp only [Functor.map_comp] at ht
    change e.functor.map (e.inverse.map α.right) ≫ e.functor.map (T.inr.app
      (e.inverse.mapArrow.obj g)) =
      e.functor.map (T.inr.app (e.inverse.mapArrow.obj f)) ≫
        e.functor.map ((T.joint.map (e.inverse.mapArrow.map α)).hom.left) at ht
    change α.right ≫ ((e.counitIso.app g.right).inv ≫ _) =
      ((e.counitIso.app f.right).inv ≫ _) ≫ e.functor.map _
    rw [← Category.assoc, he, Category.assoc, ht, ← Category.assoc]

/-- The natural projection from the transported joint middle object to the original arrow
target, using the projection of `T` followed by the counit of `e`. -/
def equivalenceProjection : equivalenceJoint V W e hF T ⋙ ExtensionCategory.middle W ⟶
    Arrow.rightFunc where
  app f := e.functor.map (T.projection.app (e.inverse.mapArrow.obj f)) ≫ (e.counitIso.app
    f.right).hom
  naturality {f g} α := by
    have he : e.functor.map (e.inverse.map α.right) ≫ (e.counitIso.app g.right).hom =
        (e.counitIso.app f.right).hom ≫ α.right := e.counitIso.hom.naturality α.right
    have ht := congrArg e.functor.map (T.projection.naturality (e.inverse.mapArrow.map α))
    simp only [Functor.map_comp] at ht
    change e.functor.map ((T.joint.map (e.inverse.mapArrow.map α)).hom.right) ≫
      e.functor.map (T.projection.app (e.inverse.mapArrow.obj g)) =
      e.functor.map (T.projection.app (e.inverse.mapArrow.obj f)) ≫ e.functor.map (e.inverse.map
        α.right) at ht
    change e.functor.map _ ≫ (e.functor.map _ ≫ (e.counitIso.app g.right).hom) =
      (e.functor.map _ ≫ (e.counitIso.app f.right).hom) ≫ α.right
    rw [← Category.assoc, ht, Category.assoc, he, ← Category.assoc]

/-- Genuine exact equivalence transports actual joint-cylinder data. -/
def JointData.ofExactEquivalence : JointData (NestedWeakEquivalences.refl W) where
  joint := equivalenceJoint V W e hF T
  exact := (ArrowCategory.mapArrow_exact W V hG).comp
    (T.exact.comp (ExtensionCategory.postcompose_exact V W hF))
  inl := equivalenceInl V W e hF T
  inr := equivalenceInr V W e hF T
  coproduct f := by
    let : e.functor.IsEquivalence := e.isEquivalence_functor
    let l := mapIsColimitOfPreservesOfIsColimit e.functor _ _ (T.coproduct
      (e.inverse.mapArrow.obj f))
    exact BinaryCofan.isColimitCompRightIso _ (e.counitIso.app f.right).inv
      (BinaryCofan.isColimitCompLeftIso _ (e.counitIso.app f.left).inv l)
  projection := equivalenceProjection V W e hF T
  factorization f := by
    change ((e.counitIso.app f.left).inv ≫ e.functor.map (T.inl.app (e.inverse.mapArrow.obj f))) ≫
      e.functor.map ((T.joint.obj (e.inverse.mapArrow.obj f)).obj.hom) ≫
      (e.functor.map (T.projection.app (e.inverse.mapArrow.obj f)) ≫ (e.counitIso.app
        f.right).hom) = f.hom
    have ht := congrArg e.functor.map (T.factorization (e.inverse.mapArrow.obj f))
    simp only [Functor.map_comp] at ht
    change e.functor.map (T.inl.app (e.inverse.mapArrow.obj f)) ≫
      e.functor.map ((T.joint.obj (e.inverse.mapArrow.obj f)).obj.hom) ≫
      e.functor.map (T.projection.app (e.inverse.mapArrow.obj f)) = e.functor.map (e.inverse.map
        f.hom) at ht
    have h : e.functor.map (e.inverse.map f.hom) ≫ (e.counitIso.app f.right).hom =
      (e.counitIso.app f.left).hom ≫ f.hom := e.counitIso.hom.naturality f.hom
    calc
      _ = (e.counitIso.app f.left).inv ≫
          (e.functor.map (T.inl.app (e.inverse.mapArrow.obj f)) ≫
            e.functor.map ((T.joint.obj (e.inverse.mapArrow.obj f)).obj.hom) ≫
            e.functor.map (T.projection.app (e.inverse.mapArrow.obj f))) ≫
          (e.counitIso.app f.right).hom := by simp only [Category.assoc]
      _ = (e.counitIso.app f.left).inv ≫ e.functor.map (e.inverse.map f.hom) ≫
          (e.counitIso.app f.right).hom := by rw [ht]
      _ = f.hom := by rw [h]; simp

  weak f := W.weq.comp_mem _ _ (hF.weak _ (T.weak (e.inverse.mapArrow.obj f)))
    (W.weq_iso _ inferInstance)
end Fibration.RowFactorization
end CategoryTheory.Waldhausen
