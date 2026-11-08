/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.WeakArrow.DualStructure

/-! # Joint reflection by the original opposite weak-arrow projections

Actual zero objects and all actual pushout squares are detected on the two
literal components. Reflection imposes no cofibration hypothesis.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/DualDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.WeakArrow
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (F : C ⥤ D)
  (hF : IsExact V.cof V.weq W.cof W.weq F)

include hF in
/-- The two original opposite projections jointly reflect actual zero objects. -/
theorem dual_isZero_of_components (X : (Obj W F)ᵒᵖ)
    (hC : IsZero ((source W F).op.obj X)) (hD : IsZero ((target W F).op.obj X)) :
    IsZero X := by
  have hc : IsZero X.unop.obj.left := hC.unop
  have hd : IsZero X.unop.obj.right := hD.unop
  suffices hx : IsZero X.unop by simpa using hx.op
  constructor
  · intro Y
    refine ⟨{default := ObjectProperty.homMk ⟨hc.to_ Y.obj.left, hd.to_ Y.obj.right,
      (hF.zero hc).eq_of_src _ _⟩, uniq := ?_}⟩
    intro f
    apply ObjectProperty.hom_ext
    exact Comma.hom_ext _ _ (hc.eq_of_src _ _) (hd.eq_of_src _ _)
  · intro Y
    refine ⟨{default := ObjectProperty.homMk ⟨hc.from_ Y.obj.left, hd.from_ Y.obj.right,
      hd.eq_of_tgt _ _⟩, uniq := ?_}⟩
    intro f
    apply ObjectProperty.hom_ext
    exact Comma.hom_ext _ _ (hc.eq_of_tgt _ _) (hd.eq_of_tgt _ _)

/-- The unchanged projections jointly reflect every actual pushout, with no
cofibration or fibration premise. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/DualDetection.lean:51" "adaptation"
    "Joint detection of all opposite weak-arrow pushouts without cofibration assumptions"]
theorem dual_isPushout_of_components {A B E Q : (Obj W F)ᵒᵖ}
    (i : A ⟶ B) (f : A ⟶ E) (g : B ⟶ Q) (j : E ⟶ Q)
    (hC : IsPushout ((source W F).op.map i) ((source W F).op.map f)
      ((source W F).op.map g) ((source W F).op.map j))
    (hD : IsPushout ((target W F).op.map i) ((target W F).op.map f)
      ((target W F).op.map g) ((target W F).op.map j)) : IsPushout i f g j := by
  apply IsPushout.of_map_of_faithful (objects W F).ι.op
  exact (FunctorComma.isPullback_of_pointwise F g.unop.hom j.unop.hom
    i.unop.hom f.unop.hom hC.unop.flip hD.unop.flip).op.flip

include hF in
/-- The literal original projections jointly reflect a binary-coproduct
universal property. Neither displayed inclusion needs to be a cofibration. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/DualDetection.lean:64" "adaptation"
    "Joint detection of actual binary coproduct universal properties"]
def dualBinaryCofanIsColimitOfComponents {A B : (Obj W F)ᵒᵖ} (s : BinaryCofan A B)
    (hC : IsColimit (BinaryCofan.mk ((source W F).op.map s.inl) ((source W F).op.map s.inr)))
    (hD : IsColimit (BinaryCofan.mk ((target W F).op.map s.inl) ((target W F).op.map s.inr))) :
    IsColimit s := by
  let Z := (waldhausenStructure V W F hF).zero
  have hz := (waldhausenStructure V W F hF).isZero.op
  have hzC : IsZero ((source W F).op.obj (op Z)) :=
    ((source_exact V W F hF).zero (waldhausenStructure V W F hF).isZero).op
  have hzD : IsZero ((target W F).op.obj (op Z)) :=
    ((target_exact V W F hF).zero (waldhausenStructure V W F hF).isZero).op
  have hp : IsPushout (hz.to_ A) (hz.to_ B) s.inl s.inr := by
    apply dual_isPushout_of_components W F
    · convert IsPushout.of_is_coproduct hC hzC.isInitial using 1 <;>
        first | rfl | exact hzC.eq_of_src _ _
    · convert IsPushout.of_is_coproduct hD hzD.isInitial using 1 <;>
        first | rfl | exact hzD.eq_of_src _ _
  exact BinaryCofan.IsColimit.mk s
    (fun a b => hp.desc a b (hz.eq_of_src _ _))
    (fun a b => hp.inl_desc a b _)
    (fun a b => hp.inr_desc a b _)
    (fun a b m hm hn => hp.hom_ext (hm.trans (hp.inl_desc a b _).symm)
      (hn.trans (hp.inr_desc a b _).symm))

end CategoryTheory.Waldhausen.WeakArrow
