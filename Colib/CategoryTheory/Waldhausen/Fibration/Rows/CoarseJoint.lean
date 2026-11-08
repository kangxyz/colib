/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ReflexiveFactorization
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Functoriality

/-! # The genuine original joint cylinder is exact for the coarse weak class

Actual endpoint coproducts and coarse gluing give coarse weakness of its
source maps. Naturality against the given coarse-weak projections gives
coarse weakness of its middle maps by two-out-of-three. Cofibrations and
actual pushouts retain the original shared cofibration data. This upgrades the
fine-exact `JointData N` to `JointData (NestedWeakEquivalences.refl N.coarse)`;
fine exactness alone would not prove this coarse exactness.

Implementation provenance: `Quillen/Waldhausen/Fibration/Rows/CoarseJoint.lean:30-114`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual functor, both endpoint maps, chosen zero, projection and independent
object and morphism universes are retained. No geometric hypothesis is used.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RowFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : JointData N)

/-- The actual endpoint sum is also the pushout over the coarse chosen zero. -/
theorem jointSource_coarse_isPushout (f : Arrow C) :
    IsPushout (N.coarse.isZero.to_ f.left) (N.coarse.isZero.to_ f.right)
      (D.inl.app f) (D.inr.app f) := by
  have hl : N.coarse.isZero.isInitial.to f.left = N.coarse.isZero.to_ f.left :=
    N.coarse.isZero.eq_of_src _ _
  have hr : N.coarse.isZero.isInitial.to f.right = N.coarse.isZero.to_ f.right :=
    N.coarse.isZero.eq_of_src _ _
  rw [← hl, ← hr]
  exact IsPushout.of_is_coproduct' (D.coproduct f) N.coarse.isZero.isInitial

/-- Actual coarse gluing, not fine exactness, controls the original source map. -/
theorem jointSource_coarseWeak {f g : Arrow C} (α : f ⟶ g)
    (hl : N.coarse.weq α.left) (hr : N.coarse.weq α.right) :
    N.coarse.weq ((D.joint.map α).hom.left) :=
  N.coarse.gluing (𝟙 N.coarse.zero) α.left α.right ((D.joint.map α).hom.left)
    (N.coarse.cof_zero f.left) (N.coarse.cof_zero g.left)
    (jointSource_coarse_isPushout N D f) (jointSource_coarse_isPushout N D g)
    (N.coarse.isZero.eq_of_src _ _) (N.coarse.isZero.eq_of_src _ _)
    (D.inl.naturality α).symm (D.inr.naturality α).symm (N.coarse.weq.id_mem _) hl hr

variable [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- The original middle map is coarse-weak by its actual weak projection square. -/
theorem jointMiddle_coarseWeak {f g : Arrow C} (α : f ⟶ g)
    (hr : N.coarse.weq α.right) : N.coarse.weq ((D.joint.map α).hom.right) := by
  apply N.coarse.weq.of_postcomp _ (D.projection.app g) (D.weak g)
  change N.coarse.weq (((D.joint ⋙ ExtensionCategory.middle V).map α) ≫ D.projection.app g)
  rw [D.projection.naturality]
  exact N.coarse.weq.comp_mem _ _ (D.weak f) hr

/-- Retarget only the proof of cofibrancy; the original joint arrow and maps stay literal. -/
def coarseJoint : Arrow C ⥤ ExtensionCategory.Obj N.coarse :=
  D.joint ⋙ ExtensionCategory.postcompose V N.coarse (changeWeak_exact N)

/-- The actual original joint functor is genuinely exact for coarse weak maps. -/
@[colib_tag "COL-0306",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/CoarseJoint.lean:30-86"
    "adaptation" "Coarse exactness by actual endpoint pushouts and weak projection naturality"]
theorem coarseJoint_exact :
    IsExact (ArrowCategory.waldhausenStructure N.coarse).cof
      (ArrowCategory.waldhausenStructure N.coarse).weq
      (ExtensionCategory.waldhausenStructure N.coarse).cof
      (ExtensionCategory.waldhausenStructure N.coarse).weq (coarseJoint N D) where
  zero h := (ExtensionCategory.postcompose_exact V N.coarse (changeWeak_exact N)).zero
    (D.exact.zero h)
  cofibration α hα := by
    have hf : (ArrowCategory.waldhausenStructure V).cof α := by
      change V.cof α.left ∧ V.cof α.right
      change N.coarse.cof α.left ∧ N.coarse.cof α.right at hα
      simpa only [N.cof_eq] using hα
    exact ExtensionCategory.postcompose_cof V N.coarse (changeWeak_exact N) (D.exact.cofibration
      α hf)
  weak α hα := ⟨jointSource_coarseWeak N D α hα.1 hα.2, jointMiddle_coarseWeak N D α hα.2⟩
  pushout {A B E P} {i f g j} hα h := by
    have hf : (ArrowCategory.waldhausenStructure V).cof i := by
      change V.cof _ ∧ V.cof _
      change N.coarse.cof _ ∧ N.coarse.cof _ at hα
      simpa only [N.cof_eq] using hα
    exact (ExtensionCategory.postcompose_exact V N.coarse (changeWeak_exact N)).pushout
      (D.exact.cofibration _ hf) (D.exact.pushout hf h)

/-- Honest joint-cylinder data for the reflexive coarse structure, preserving
both original endpoints and the original coarse-weak projection exactly. -/
@[colib_tag "COL-0306",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/CoarseJoint.lean:88-114"
    "adaptation" "Reflexive coarse joint data with the unchanged joint arrow and endpoint maps"]
def JointData.coarseReflexive : JointData (NestedWeakEquivalences.refl N.coarse) where
  joint := coarseJoint N D
  exact := coarseJoint_exact N D
  inl := D.inl
  inr := D.inr
  coproduct := D.coproduct
  projection := D.projection
  factorization := D.factorization
  weak := D.weak

/-- The first endpoint inclusion is exactly the original one. -/
@[simp] theorem coarseReflexive_inl (f : Arrow C) :
    (D.coarseReflexive N).inl.app f = D.inl.app f := rfl

/-- The second endpoint inclusion is exactly the original one. -/
@[simp] theorem coarseReflexive_inr (f : Arrow C) :
    (D.coarseReflexive N).inr.app f = D.inr.app f := rfl

/-- The coarse cylinder retains the literal original projection. -/
@[simp] theorem coarseReflexive_projection (f : Arrow C) :
    (D.coarseReflexive N).projection.app f = D.projection.app f := rfl

/-- The actual joint cofibration arrow is unchanged. -/
@[simp] theorem coarseReflexive_joint_hom (f : Arrow C) :
    ((D.coarseReflexive N).joint.obj f).obj.hom = (D.joint.obj f).obj.hom := rfl

/-- The source component of every joint map is unchanged. -/
@[simp] theorem coarseReflexive_joint_map_left {f g : Arrow C} (α : f ⟶ g) :
    ((D.coarseReflexive N).joint.map α).hom.left = (D.joint.map α).hom.left := rfl

/-- The middle component of every joint map is unchanged. -/
@[simp] theorem coarseReflexive_joint_map_right {f g : Arrow C} (α : f ⟶ g) :
    ((D.coarseReflexive N).joint.map α).hom.right = (D.joint.map α).hom.right := rfl

end CategoryTheory.Waldhausen.Fibration.RowFactorization
