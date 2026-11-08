/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.Comma.Basic

/-!
# Genuine componentwise Waldhausen comma categories

An exact functor F gives the actual comma category of arrows F(A)→B.
Component pushouts are constructed from genuine source and target pushouts,
with preservation of the source square supplied by the original exact functor.
Every chosen pushout is proved pointwise. Both projections are genuinely exact;
no ambient cocompleteness, approximation or K-equivalence is assumed.

Implementation provenance: `Quillen/Waldhausen/CommaCategory/Structure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.FunctorComma
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (F : C ⥤ D)
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The comma category of arrows `F.obj A ⟶ B`, with morphisms given by commutative squares. -/
abbrev Obj := Comma F (𝟭 D)

/-- Comma morphisms whose source-category component lies in `V.cof` and whose target-category
component lies in `W.cof`. -/
def cof : MorphismProperty (Obj F) :=
  V.cof.inverseImage (Comma.fst F (𝟭 D)) ⊓ W.cof.inverseImage (Comma.snd F (𝟭 D))
/-- Comma morphisms whose source-category component lies in `V.weq` and whose target-category
component lies in `W.weq`. -/
def weq : MorphismProperty (Obj F) :=
  V.weq.inverseImage (Comma.fst F (𝟭 D)) ⊓ W.weq.inverseImage (Comma.snd F (𝟭 D))
instance cof_multiplicative : (cof V W F).IsMultiplicative := by unfold cof; infer_instance
instance weq_multiplicative : (weq V W F).IsMultiplicative := by unfold weq; infer_instance

/-- The identity of `F.obj V.zero`, viewed as a comma object with source `V.zero`; exactness of
`F` makes this a zero object. -/
def zero : Obj F := ⟨V.zero, F.obj V.zero, 𝟙 _⟩

include hF in
theorem isZero : IsZero (zero V F) where
  unique_to X := by
    refine ⟨{default := ⟨V.isZero.to_ X.left, (hF.zero V.isZero).to_ X.right,
      (hF.zero V.isZero).eq_of_src _ _⟩, uniq := ?_}⟩
    intro f
    apply Comma.hom_ext
    · exact V.isZero.eq_of_src _ _
    · exact (hF.zero V.isZero).eq_of_src _ _
  unique_from X := by
    refine ⟨{default := ⟨V.isZero.from_ X.left, (hF.zero V.isZero).from_ X.right,
      (hF.zero V.isZero).eq_of_tgt _ _⟩, uniq := ?_}⟩
    intro f
    apply Comma.hom_ext
    · exact V.isZero.eq_of_tgt _ _
    · exact (hF.zero V.isZero).eq_of_tgt _ _

/-- Genuine component pushouts give a comma pushout when the source square is preserved. -/
theorem isPushout_of_pointwise {A B E P : Obj F}
    (f : A ⟶ B) (g : A ⟶ E) (i : B ⟶ P) (j : E ⟶ P)
    (hl : IsPushout f.left g.left i.left j.left)
    (hFl : IsPushout (F.map f.left) (F.map g.left) (F.map i.left) (F.map j.left))
    (hr : IsPushout f.right g.right i.right j.right) : IsPushout f g i j := by
  have w : f ≫ i = g ≫ j := Comma.hom_ext _ _ hl.w hr.w
  let l (s : PushoutCocone f g) := hl.desc s.inl.left s.inr.left
    (congrArg CommaMorphism.left s.condition)
  let r (s : PushoutCocone f g) := hr.desc s.inl.right s.inr.right
    (congrArg CommaMorphism.right s.condition)
  have wh (s : PushoutCocone f g) : F.map (l s) ≫ s.pt.hom = P.hom ≫ r s := by
    apply hFl.hom_ext
    · rw [← Category.assoc, ← F.map_comp]
      dsimp [l]
      rw [hl.inl_desc]
      rw [← Category.assoc, i.w, Category.assoc]
      dsimp [r]
      rw [hr.inl_desc]
      exact s.inl.w
    · rw [← Category.assoc, ← F.map_comp]
      dsimp [l]
      rw [hl.inr_desc]
      rw [← Category.assoc, j.w, Category.assoc]
      dsimp [r]
      rw [hr.inr_desc]
      exact s.inr.w
  let d (s : PushoutCocone f g) : P ⟶ s.pt := ⟨l s, r s, wh s⟩
  have hi (s : PushoutCocone f g) : i ≫ d s = s.inl := by
    apply Comma.hom_ext
    · exact hl.inl_desc _ _ _
    · exact hr.inl_desc _ _ _
  have hj (s : PushoutCocone f g) : j ≫ d s = s.inr := by
    apply Comma.hom_ext
    · exact hl.inr_desc _ _ _
    · exact hr.inr_desc _ _ _
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i j w)
  refine PushoutCocone.IsColimit.mk w d hi hj ?_
  intro s m hm hn
  apply Comma.hom_ext
  · apply hl.hom_ext
    · exact (congrArg CommaMorphism.left hm).trans (congrArg CommaMorphism.left (hi s)).symm
    · exact (congrArg CommaMorphism.left hn).trans (congrArg CommaMorphism.left (hj s)).symm
  · apply hr.hom_ext
    · exact (congrArg CommaMorphism.right hm).trans (congrArg CommaMorphism.right (hi s)).symm
    · exact (congrArg CommaMorphism.right hn).trans (congrArg CommaMorphism.right (hj s)).symm

include hF in
/-- Actual component pushouts construct the pointwise comma pushout. -/
theorem exists_pointwise_pushout {A B E : Obj F} (f : A ⟶ B) (g : A ⟶ E)
    (hf : cof V W F f) :
    ∃ (P : Obj F) (i : B ⟶ P) (j : E ⟶ P), IsPushout f g i j ∧
      IsPushout f.left g.left i.left j.left ∧ IsPushout f.right g.right i.right j.right := by
  obtain ⟨L, li, lj, hL⟩ := V.pushout_exists f.left g.left hf.1
  obtain ⟨R, ri, rj, hR⟩ := W.pushout_exists f.right g.right hf.2
  have hFL : IsPushout (F.map f.left) (F.map g.left) (F.map li) (F.map lj) :=
    hF.pushout hf.1 hL
  let p : F.obj L ⟶ R := hFL.desc (B.hom ≫ ri) (E.hom ≫ rj) (by
    calc
      F.map f.left ≫ B.hom ≫ ri = A.hom ≫ f.right ≫ ri := by
        simpa only [Category.assoc, Functor.id_map] using congrArg (fun k => k ≫ ri) f.w
      _ = A.hom ≫ g.right ≫ rj := by rw [hR.w]
      _ = F.map g.left ≫ E.hom ≫ rj := by
        simpa only [Category.assoc, Functor.id_map] using (congrArg (fun k => k ≫ rj) g.w).symm)
  let P : Obj F := ⟨L, R, p⟩
  let i : B ⟶ P := ⟨li, ri, hFL.inl_desc _ _ _⟩
  let j : E ⟶ P := ⟨lj, rj, hFL.inr_desc _ _ _⟩
  exact ⟨P, i, j, isPushout_of_pointwise F f g i j hL hFL hR, hL, hR⟩

include hF in
/-- Every original comma pushout along a pointwise cofibration is pointwise. -/
theorem pointwise_of_isPushout {A B E P : Obj F}
    {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ P} {j : E ⟶ P}
    (hf : cof V W F f) (h : IsPushout f g i j) :
    IsPushout f.left g.left i.left j.left ∧ IsPushout f.right g.right i.right j.right := by
  obtain ⟨P₀, i₀, j₀, h₀, hl, hr⟩ := exists_pointwise_pushout V W F hF f g hf
  let e : P₀ ≅ P := h₀.isoIsPushout _ _ h
  constructor
  · apply hl.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((Comma.fst F (𝟭 D)).mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg CommaMorphism.left (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg CommaMorphism.left (h₀.inr_isoIsPushout_hom _ _ h)
  · apply hr.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((Comma.snd F (𝟭 D)).mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg CommaMorphism.right (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg CommaMorphism.right (h₀.inr_isoIsPushout_hom _ _ h)

/-- The original comma category with both componentwise map classes. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/CommaCategory/Structure.lean:162" "adaptation"
    "Componentwise comma Waldhausen structure on the literal Comma F (𝟭 D)"]
def waldhausenStructure : Structure (Obj F) where
  zero := zero V F
  isZero := isZero V W F hF
  cof := cof V W F
  weq := weq V W F
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact ⟨V.cof_iso _ (inferInstance : IsIso ((Comma.fst F (𝟭 D)).map f)),
      W.cof_iso _ (inferInstance : IsIso ((Comma.snd F (𝟭 D)).map f))⟩
  weq_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact ⟨V.weq_iso _ (inferInstance : IsIso ((Comma.fst F (𝟭 D)).map f)),
      W.weq_iso _ (inferInstance : IsIso ((Comma.snd F (𝟭 D)).map f))⟩
  cof_zero X := by
    have hl : ((isZero V W F hF).to_ X).left = V.isZero.to_ X.left := V.isZero.eq_of_src _ _
    have hr : ((isZero V W F hF).to_ X).right = (hF.zero V.isZero).to_ X.right :=
      (hF.zero V.isZero).eq_of_src _ _
    change V.cof ((isZero V W F hF).to_ X).left ∧ W.cof ((isZero V W F hF).to_ X).right
    rw [hl, hr]
    refine ⟨V.cof_zero _, ?_⟩
    have e := (hF.zero V.isZero).iso W.isZero
    have he : (hF.zero V.isZero).to_ X.right = e.hom ≫ W.isZero.to_ X.right :=
      (hF.zero V.isZero).eq_of_src _ _
    rw [he]
    exact W.cof.comp_mem _ _ (W.cof_iso _ inferInstance) (W.cof_zero _)
  pushout_exists f g hf := by
    obtain ⟨P, i, j, h, _, _⟩ := exists_pointwise_pushout V W F hF f g hf
    exact ⟨P, i, j, h⟩
  cof_pushout hf h :=
    ⟨V.cof_pushout hf.1 (pointwise_of_isPushout V W F hF hf h).1,
      W.cof_pushout hf.2 (pointwise_of_isPushout V W F hF hf h).2⟩
  gluing := by
    intro A B E P A' B' E' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd
    obtain ⟨hl, hr⟩ := pointwise_of_isPushout V W F hF hf h
    obtain ⟨hl', hr'⟩ := pointwise_of_isPushout V W F hF hf' h'
    exact ⟨V.gluing a.left b.left d.left p.left hf.1 hf'.1 hl hl'
      (congrArg CommaMorphism.left ef) (congrArg CommaMorphism.left eg)
      (congrArg CommaMorphism.left ei) (congrArg CommaMorphism.left ej) ha.1 hb.1 hd.1,
      W.gluing a.right b.right d.right p.right hf.2 hf'.2 hr hr'
      (congrArg CommaMorphism.right ef) (congrArg CommaMorphism.right eg)
      (congrArg CommaMorphism.right ei) (congrArg CommaMorphism.right ej) ha.2 hb.2 hd.2⟩

/-- The literal source projection preserves zero objects, both map classes and pushouts. -/
theorem source_exact : IsExact (waldhausenStructure V W F hF).cof
    (waldhausenStructure V W F hF).weq V.cof V.weq (Comma.fst F (𝟭 D)) where
  zero h := V.isZero.of_iso ((Comma.fst F (𝟭 D)).mapIso (h.iso (isZero V W F hF)))
  cofibration _ h := h.1
  weak _ h := h.1
  pushout hf h := (pointwise_of_isPushout V W F hF hf h).1

/-- The literal target projection preserves zero objects, both map classes and pushouts. -/
theorem target_exact : IsExact (waldhausenStructure V W F hF).cof
    (waldhausenStructure V W F hF).weq W.cof W.weq (Comma.snd F (𝟭 D)) where
  zero h := (hF.zero V.isZero).of_iso ((Comma.snd F (𝟭 D)).mapIso (h.iso (isZero V W F hF)))
  cofibration _ h := h.2
  weak _ h := h.2
  pushout hf h := (pointwise_of_isPushout V W F hF hf h).2
end CategoryTheory.Waldhausen.FunctorComma
