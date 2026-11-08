/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.CofibrationSequence
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.CategoryTheory.Waldhausen.Rows.OneRow

/-!
# The literal identity-to-chosen-zero cofibration sequence

Implementation provenance: Quillen/Waldhausen/Additivity/IdentitySequence.lean:28-74
at c561118b7795eb9780be9ed391c3251d6a4d0afd.

The existing chosen-zero transformation is retained. The actual relative pushout comparison
is the inverse of its target inclusion, so the identity transformation satisfies the genuine
relative cofibration condition. The original zero-corner square is a horizontal identity pushout.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure D) (F : C ⥤ D)

/-- The actual relative pushout target inclusion is invertible for the identity transformation. -/
theorem identityTargetInclusion_isIso {X Y : C} (f : X ⟶ Y) :
    IsIso (targetι W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) (Arrow.mk f)) := by
  let : HasPushout (𝟙 (F.obj X)) (F.map f) :=
    hasPushout W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) f
  change IsIso (pushout.inr (𝟙 (F.obj X)) (F.map f))
  infer_instance

/-- The comparison isomorphism is exactly the inverse of the original target inclusion. -/
def identityPushoutComparisonIso {X Y : C} (f : X ⟶ Y) :
    (pushoutFunctor W (𝟙 F) (fun X => W.cof.id_mem (F.obj X))).obj (Arrow.mk f) ≅ F.obj Y := by
  letI := identityTargetInclusion_isIso W F f
  exact (asIso (targetι W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) (Arrow.mk f))).symm

/-- Its forward map is the unchanged relative pushout comparison. -/
theorem identityPushoutComparisonIso_hom {X Y : C} (f : X ⟶ Y) :
    (identityPushoutComparisonIso W F f).hom =
      comparison W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) (Arrow.mk f) := by
  let := identityTargetInclusion_isIso W F f
  apply (cancel_epi (targetι W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) (Arrow.mk f))).1
  exact (IsIso.hom_inv_id _).trans
    (targetι_comparison W (𝟙 F) (fun X => W.cof.id_mem (F.obj X)) (Arrow.mk f)).symm

variable (V : Structure C)

/-- Identity satisfies the actual relative cofibration condition for every source structure. -/
theorem identityCofibrationTransformation : IsCofibrationTransformation W (𝟙 F) V where
  app_cof X := W.cof.id_mem (F.obj X)
  relative_cof f _ := by
    rw [← identityPushoutComparisonIso_hom W F f]
    exact W.cof_iso _ inferInstance

/-- Every exact functor has its literal identity-to-chosen-zero cofibration sequence. -/
theorem identityCofibrationSequence
    (hF : IsExact V.cof V.weq W.cof W.weq F) :
    IsCofibrationSequence V W (𝟙 F)
      (Functor.whiskerLeft F (QuotientRows.oneIdToZero W)) where
  exactF := hF
  exactG := hF
  exactH := hF.comp (zeroFunctor_isExact W W)
  cofibration := identityCofibrationTransformation W F V
  cofiber X := by
    change IsPushout (𝟙 (F.obj X)) (W.isZero.from_ (F.obj X))
      (W.isZero.from_ (F.obj X)) (W.isZero.to_ W.zero)
    rw [show W.isZero.to_ W.zero = 𝟙 W.zero from W.isZero.eq_of_src _ _]
    exact IsPushout.id_horiz _

end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Additivity/IdentitySequence.lean:28-74"
  "adaptation" "The actual identity sequence through the original chosen zero"]
  CategoryTheory.Waldhausen.Additivity.identityCofibrationSequence
