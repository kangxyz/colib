/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.CommaCategory.Structure
public import Colib.CategoryTheory.Waldhausen.Duality.Basic

/-! # Actual opposite comma Waldhausen structures

The underlying category is exactly the opposite of the existing comma of
original arrows F(A)→B. Genuine pointwise pullbacks give its pushouts, with
both original projection functors retained literally.

Implementation provenance: `Quillen/Waldhausen/CommaCategory/DualStructure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen

namespace FunctorComma
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
  (F : C ⥤ D) (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- Cofibrations in the opposite comma category, detected on both opposite projection functors
by `Vd.cof` and `Wd.cof`. -/
def dualCof : MorphismProperty (Obj F)ᵒᵖ :=
  Vd.cof.inverseImage (Comma.fst F (𝟭 D)).op ⊓ Wd.cof.inverseImage (Comma.snd F (𝟭 D)).op
/-- Weak equivalences in the opposite comma category, detected on both opposite projection
functors by `Vd.weq` and `Wd.weq`. -/
def dualWeq : MorphismProperty (Obj F)ᵒᵖ :=
  Vd.weq.inverseImage (Comma.fst F (𝟭 D)).op ⊓ Wd.weq.inverseImage (Comma.snd F (𝟭 D)).op

/-- Original pointwise pullbacks give the genuine comma pullback. -/
theorem isPullback_of_pointwise {P B E A : Obj F}
    (i : P ⟶ B) (j : P ⟶ E) (f : B ⟶ A) (g : E ⟶ A)
    (hl : IsPullback i.left j.left f.left g.left)
    (hr : IsPullback i.right j.right f.right g.right) : IsPullback i j f g := by
  refine IsPullback.mk' (Comma.hom_ext _ _ hl.w hr.w) ?_ ?_
  · intro T a b hai haj
    apply Comma.hom_ext
    · exact hl.hom_ext (congrArg CommaMorphism.left hai) (congrArg CommaMorphism.left haj)
    · exact hr.hom_ext (congrArg CommaMorphism.right hai) (congrArg CommaMorphism.right haj)
  · intro T a b hab
    let l := hl.lift a.left b.left (congrArg CommaMorphism.left hab)
    let r := hr.lift a.right b.right (congrArg CommaMorphism.right hab)
    have hw : F.map l ≫ P.hom = T.hom ≫ r := by
      apply hr.hom_ext
      · calc
          (F.map l ≫ P.hom) ≫ i.right = F.map l ≫ F.map i.left ≫ B.hom := by
            simpa only [Category.assoc, Functor.id_map] using congrArg (fun k => F.map l ≫ k)
              i.w.symm
          _ = F.map a.left ≫ B.hom := by rw [← Category.assoc, ← F.map_comp, hl.lift_fst]
          _ = T.hom ≫ a.right := a.w
          _ = (T.hom ≫ r) ≫ i.right := by simp [r]
      · calc
          (F.map l ≫ P.hom) ≫ j.right = F.map l ≫ F.map j.left ≫ E.hom := by
            simpa only [Category.assoc, Functor.id_map] using congrArg (fun k => F.map l ≫ k)
              j.w.symm
          _ = F.map b.left ≫ E.hom := by rw [← Category.assoc, ← F.map_comp, hl.lift_snd]
          _ = T.hom ≫ b.right := b.w
          _ = (T.hom ≫ r) ≫ j.right := by simp [r]
    refine ⟨⟨l, r, hw⟩, ?_, ?_⟩
    · exact Comma.hom_ext _ _ (hl.lift_fst _ _ _) (hr.lift_fst _ _ _)
    · exact Comma.hom_ext _ _ (hl.lift_snd _ _ _) (hr.lift_snd _ _ _)

/-- Original component pullbacks construct actual opposite-comma pushouts. -/
theorem exists_pointwise_dual_pushout {A B E : (Obj F)ᵒᵖ}
    (f : A ⟶ B) (g : A ⟶ E) (hf : dualCof Vd Wd F f) :
    ∃ (P : (Obj F)ᵒᵖ) (i : B ⟶ P) (j : E ⟶ P), IsPushout f g i j ∧
      IsPushout f.unop.left.op g.unop.left.op i.unop.left.op j.unop.left.op ∧
      IsPushout f.unop.right.op g.unop.right.op i.unop.right.op j.unop.right.op := by
  obtain ⟨L, li, lj, hL⟩ := Vd.pushout_exists f.unop.left.op g.unop.left.op hf.1
  obtain ⟨R, ri, rj, hR⟩ := Wd.pushout_exists f.unop.right.op g.unop.right.op hf.2
  have hl := hL.unop.flip
  have hr := hR.unop.flip
  let p : F.obj L.unop ⟶ R.unop := hr.lift
    (F.map li.unop ≫ B.unop.hom) (F.map lj.unop ≫ E.unop.hom) (by
      calc
        (F.map li.unop ≫ B.unop.hom) ≫ f.unop.right =
            F.map li.unop ≫ F.map f.unop.left ≫ A.unop.hom := by
          simpa only [Category.assoc, Functor.id_map] using
            congrArg (fun k => F.map li.unop ≫ k) f.unop.w.symm
        _ = F.map (li.unop ≫ f.unop.left) ≫ A.unop.hom := by rw [F.map_comp, Category.assoc]
        _ = F.map (lj.unop ≫ g.unop.left) ≫ A.unop.hom := by
          exact congrArg (fun k => F.map k ≫ A.unop.hom) hl.w
        _ = (F.map lj.unop ≫ E.unop.hom) ≫ g.unop.right := by
          simpa only [F.map_comp, Category.assoc, Functor.id_map] using
            congrArg (fun k => F.map lj.unop ≫ k) g.unop.w)
  let P : Obj F := ⟨L.unop, R.unop, p⟩
  let i : P ⟶ B.unop := ⟨li.unop, ri.unop, (hr.lift_fst _ _ _).symm⟩
  let j : P ⟶ E.unop := ⟨lj.unop, rj.unop, (hr.lift_snd _ _ _).symm⟩
  exact ⟨op P, i.op, j.op, (isPullback_of_pointwise F i j f.unop g.unop hl hr).op.flip, hL, hR⟩

/-- Every actual opposite-comma pushout along a componentwise fibration is pointwise. -/
theorem pointwise_of_dual_isPushout {A B E P : (Obj F)ᵒᵖ}
    {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ P} {j : E ⟶ P}
    (hf : dualCof Vd Wd F f) (h : IsPushout f g i j) :
    IsPushout f.unop.left.op g.unop.left.op i.unop.left.op j.unop.left.op ∧
      IsPushout f.unop.right.op g.unop.right.op i.unop.right.op j.unop.right.op := by
  obtain ⟨P₀, i₀, j₀, h₀, hl, hr⟩ := exists_pointwise_dual_pushout Vd Wd F f g hf
  let e : P₀ ≅ P := h₀.isoIsPushout _ _ h
  constructor
  · apply hl.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (((Comma.fst F (𝟭 D)).op).mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun k => k.unop.left.op) (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun k => k.unop.left.op) (h₀.inr_isoIsPushout_hom _ _ h)
  · apply hr.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (((Comma.snd F (𝟭 D)).op).mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun k => k.unop.right.op) (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun k => k.unop.right.op) (h₀.inr_isoIsPushout_hom _ _ h)

/-- The genuine opposite Waldhausen structure on the unchanged comma category. -/
def dualWaldhausenStructure : Structure (Obj F)ᵒᵖ where
  zero := op (zero V F)
  isZero := (isZero V W F hF).op
  cof := dualCof Vd Wd F
  weq := dualWeq Vd Wd F
  cof_multiplicative := by unfold dualCof; infer_instance
  weq_multiplicative := by unfold dualWeq; infer_instance
  cof_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact ⟨Vd.cof_iso _ (inferInstance : IsIso (((Comma.fst F (𝟭 D)).op).map f)),
      Wd.cof_iso _ (inferInstance : IsIso (((Comma.snd F (𝟭 D)).op).map f))⟩
  weq_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact ⟨Vd.weq_iso _ (inferInstance : IsIso (((Comma.fst F (𝟭 D)).op).map f)),
      Wd.weq_iso _ (inferInstance : IsIso (((Comma.snd F (𝟭 D)).op).map f))⟩
  cof_zero X := ⟨Vd.cof_of_isZero V.isZero.op _, Wd.cof_of_isZero (hF.zero V.isZero).op _⟩
  pushout_exists f g hf := by
    obtain ⟨P, i, j, h, _, _⟩ := exists_pointwise_dual_pushout Vd Wd F f g hf
    exact ⟨P, i, j, h⟩
  cof_pushout hf h :=
    ⟨Vd.cof_pushout hf.1 (pointwise_of_dual_isPushout Vd Wd F hf h).1,
      Wd.cof_pushout hf.2 (pointwise_of_dual_isPushout Vd Wd F hf h).2⟩
  gluing := by
    intro A B E P A' B' E' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd
    obtain ⟨hl, hr⟩ := pointwise_of_dual_isPushout Vd Wd F hf h
    obtain ⟨hl', hr'⟩ := pointwise_of_dual_isPushout Vd Wd F hf' h'
    exact ⟨Vd.gluing a.unop.left.op b.unop.left.op d.unop.left.op p.unop.left.op hf.1 hf'.1 hl hl'
      (congrArg (fun k => k.unop.left.op) ef) (congrArg (fun k => k.unop.left.op) eg)
      (congrArg (fun k => k.unop.left.op) ei) (congrArg (fun k => k.unop.left.op) ej) ha.1 hb.1
        hd.1,
      Wd.gluing a.unop.right.op b.unop.right.op d.unop.right.op p.unop.right.op hf.2 hf'.2 hr hr'
      (congrArg (fun k => k.unop.right.op) ef) (congrArg (fun k => k.unop.right.op) eg)
      (congrArg (fun k => k.unop.right.op) ei) (congrArg (fun k => k.unop.right.op) ej) ha.2
        hb.2 hd.2⟩

/-- The actual opposite source projection preserves the dual Waldhausen structure. -/
theorem dual_source_exact : IsExact (dualWaldhausenStructure V W Vd Wd F hF).cof
    (dualWaldhausenStructure V W Vd Wd F hF).weq Vd.cof Vd.weq (Comma.fst F (𝟭 D)).op where
  zero h := V.isZero.op.of_iso (((Comma.fst F (𝟭 D)).op).mapIso (h.iso (isZero V W F hF).op))
  cofibration _ h := h.1
  weak _ h := h.1
  pushout hf h := (pointwise_of_dual_isPushout Vd Wd F hf h).1

/-- The actual opposite target projection preserves the dual Waldhausen structure. -/
theorem dual_target_exact : IsExact (dualWaldhausenStructure V W Vd Wd F hF).cof
    (dualWaldhausenStructure V W Vd Wd F hF).weq Wd.cof Wd.weq (Comma.snd F (𝟭 D)).op where
  zero h := (hF.zero V.isZero).op.of_iso (((Comma.snd F (𝟭 D)).op).mapIso
    (h.iso (isZero V W F hF).op))
  cofibration _ h := h.2
  weak _ h := h.2
  pushout hf h := (pointwise_of_dual_isPushout Vd Wd F hf h).2

/-- Actual component kernel–cokernel squares prove duality on the original comma. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/CommaCategory/DualStructure.lean:180" "adaptation"
    "Actual opposite comma structure and zero-corner cofiber/fiber compatibility"]
theorem dual_compatible (hV : IsCompatibleDual V Vd) (hW : IsCompatibleDual W Wd) :
    IsCompatibleDual (waldhausenStructure V W F hF)
      (dualWaldhausenStructure V W Vd Wd F hF) where
  weak f := and_congr (hV.weak f.left) (hW.weak f.right)
  cofiber i z q s hZ := by
    have hzL := (source_exact V W F hF).zero hZ
    have hzR := (target_exact V W F hF).zero hZ
    constructor
    · rintro ⟨hi, hp⟩
      obtain ⟨hl, hr⟩ := pointwise_of_isPushout V W F hF hi hp
      obtain ⟨hql, hpl⟩ := (hV.cofiber _ _ _ _ hzL).mp ⟨hi.1, hl⟩
      obtain ⟨hqr, hpr⟩ := (hW.cofiber _ _ _ _ hzR).mp ⟨hi.2, hr⟩
      exact ⟨⟨hql, hqr⟩, isPullback_of_pointwise F i z q s hpl hpr⟩
    · rintro ⟨hq, hp⟩
      obtain ⟨hl, hr⟩ := pointwise_of_dual_isPushout Vd Wd F hq hp.op.flip
      obtain ⟨hil, hpl⟩ := (hV.cofiber _ _ _ _ hzL).mpr ⟨hq.1, hl.unop.flip⟩
      obtain ⟨hir, hpr⟩ := (hW.cofiber _ _ _ _ hzR).mpr ⟨hq.2, hr.unop.flip⟩
      exact ⟨⟨hil, hir⟩, isPushout_of_pointwise F i z q s hpl (hF.pushout hil hpl) hpr⟩

end FunctorComma
end CategoryTheory.Waldhausen
