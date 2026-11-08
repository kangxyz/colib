/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.WeakArrow.JointExact
public import Colib.CategoryTheory.Waldhausen.WeakArrow.JointEndpoints
/-! # Coherent component joint data on original opposite weak arrows

The specified component compatibility retains each endpoint and projection.
Actual reflected coproducts, original factorization and the weak projection
complete the genuine joint-data structure.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/JointData.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original hypotheses, functors, component maps and independent universes are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.WeakArrow
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

/-- Coherent genuine component joint data gives actual original opposite
weak-arrow joint data, including its coproduct and endpoint maps. -/
@[colib_tag "COL-0310",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/JointData.lean:41-56" "adaptation"
    "Genuine opposite weak-arrow joint data from coherent component joint data"]
def dualJointData : Fibration.RowFactorization.JointData
    (Fibration.NestedWeakEquivalences.refl (dualWaldhausenStructure V W Vd Wd F hF hFd hW)) where
  joint := jointFunctor W Wd F hW V Vd hF hFd Tc Td compat
  exact := jointFunctor_exact V W Vd Wd F hF hFd hW Tc Td compat
  inl := { app := fun f => (jointInl W F Wd hW Vd hFd Tc Td compat hinl).app f
           naturality := fun {_ _} α => (jointInl W F Wd hW Vd hFd Tc Td compat hinl).naturality α }
  inr := { app := fun f => (jointInr W F Wd hW Vd hFd Tc Td compat hinr).app f
           naturality := fun {_ _} α => (jointInr W F Wd hW Vd hFd Tc Td compat hinr).naturality α }
  coproduct f := dualBinaryCofanIsColimitOfComponents V W F hF _
    (Tc.coproduct ((source W F).op.mapArrow.obj f))
    (Td.coproduct ((target W F).op.mapArrow.obj f))
  projection := { app := fun f => (jointProjection W F Wd hW Vd hFd Tc Td compat hproj).app f
                  naturality := fun {_ _} α => (jointProjection W F Wd hW Vd hFd Tc Td compat
                    hproj).naturality α }
  factorization := joint_factorization W F Wd hW Vd hFd Tc Td compat hinl hproj
  weak := jointProjection_weak W F Wd hW V Vd hF hFd Tc Td compat hproj
end CategoryTheory.Waldhausen.WeakArrow
