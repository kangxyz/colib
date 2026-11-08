/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.CommaCategory.DualStructure
public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory.Opposite
public import Colib.CategoryTheory.Waldhausen.WeakArrow.Structure

/-! # The genuine dual weak-arrow Waldhausen structure

Original weak arrows F(A)→B are closed under actual componentwise fibration
pullbacks. The opposite category retains those original objects and arrows,
and its cofibrations and weak maps are exactly componentwise.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/DualStructure.lean`
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
  (V : Structure C) (W : Structure D) (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
  (F : C ⥤ D) (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (hW : IsCompatibleDual W Wd)

include hFd hW
/-- Genuine pullback gluing preserves the original stored weak arrow. -/
theorem dual_closed : CofibrationClosedSubcategory.Closed
    (FunctorComma.dualWaldhausenStructure V W Vd Wd F hF) (objects W F).op where
  zero_mem := W.weq.id_mem _
  pushout_mem {A B E P} {f g i j} hf h hA hB hE := by
    obtain ⟨hl, hr⟩ := FunctorComma.pointwise_of_dual_isPushout Vd Wd F hf h
    apply (hW.weak P.unop.hom).mpr
    exact Wd.gluing A.unop.hom.op B.unop.hom.op E.unop.hom.op P.unop.hom.op
      hf.2 (hFd.cofibration _ hf.1) hr (hFd.pushout hf.1 hl)
      (congrArg Quiver.Hom.op f.unop.w).symm (congrArg Quiver.Hom.op g.unop.w).symm
      (congrArg Quiver.Hom.op i.unop.w).symm (congrArg Quiver.Hom.op j.unop.w).symm
      ((hW.weak _).mp hA) ((hW.weak _).mp hB) ((hW.weak _).mp hE)

/-- The opposite of the original weak-arrow category, with unchanged component classes. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/DualStructure.lean:47" "adaptation"
    "Opposite weak-arrow structure with the original component fibration and weak classes"]
def dualWaldhausenStructure : Structure (Obj W F)ᵒᵖ :=
  CofibrationClosedSubcategory.oppositeStructure
    (FunctorComma.dualWaldhausenStructure V W Vd Wd F hF) (objects W F)
    (dual_closed V W Vd Wd F hF hFd hW)

/-- Detection of cofibrations is exactly the two original component fibration tests. -/
@[simp] theorem dual_cof_iff {X Y : (Obj W F)ᵒᵖ} (f : X ⟶ Y) :
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof f ↔
      Vd.cof f.unop.hom.left.op ∧ Wd.cof f.unop.hom.right.op := Iff.rfl

/-- Detection of weak maps is exactly the two original component weak tests. -/
@[simp] theorem dual_weq_iff {X Y : (Obj W F)ᵒᵖ} (f : X ⟶ Y) :
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).weq f ↔
      Vd.weq f.unop.hom.left.op ∧ Wd.weq f.unop.hom.right.op := Iff.rfl

/-- The first original projection remains exact after taking opposites. -/
theorem dual_source_exact : IsExact (dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).weq Vd.cof Vd.weq (source W F).op :=
  (CofibrationClosedSubcategory.opposite_inclusion_exact _ _
    (dual_closed V W Vd Wd F hF hFd hW)).comp
    (FunctorComma.dual_source_exact V W Vd Wd F hF)

/-- The second original projection remains exact after taking opposites. -/
theorem dual_target_exact : IsExact (dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).weq Wd.cof Wd.weq (target W F).op :=
  (CofibrationClosedSubcategory.opposite_inclusion_exact _ _
    (dual_closed V W Vd Wd F hF hFd hW)).comp
    (FunctorComma.dual_target_exact V W Vd Wd F hF)

/-- Original component dualities induce duality on the actual weak-arrow category. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/DualStructure.lean:77" "adaptation"
    "Compatible dual structure on the literal weak-arrow full subcategory"]
theorem dual_compatible (hV : IsCompatibleDual V Vd) :
    IsCompatibleDual (waldhausenStructure V W F hF)
      (dualWaldhausenStructure V W Vd Wd F hF hFd hW) :=
  CofibrationClosedSubcategory.opposite_compatible _ (objects W F)
    (dual_closed V W Vd Wd F hF hFd hW) _
    (FunctorComma.dual_compatible V W Vd Wd F hF hV hW)
    (closed V W F hF)

end CategoryTheory.Waldhausen.WeakArrow
