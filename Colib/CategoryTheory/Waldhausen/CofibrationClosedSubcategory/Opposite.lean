/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Colib.CategoryTheory.Waldhausen.Duality.Basic

/-! # An inherited Waldhausen structure on the literal opposite full subcategory

Implementation provenance: `Quillen/Waldhausen/CofibrationClosedSubcategory/Opposite.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.CofibrationClosedSubcategory
variable {C : Type u} [Category.{v} C] (Wd : Structure Cᵒᵖ) (P : ObjectProperty C)
  (H : Closed Wd P.op)

/-- Transport across the strict opposite-full-subcategory equivalence keeps the
original opposite objects, original maps, and original ambient map classes. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/CofibrationClosedSubcategory/Opposite.lean:26"
    "adaptation"
    "Inherited Waldhausen structure on the literal opposite full subcategory"]
def oppositeStructure : Structure P.FullSubcategoryᵒᵖ where
  zero := op ⟨Wd.zero.unop, H.zero_mem⟩
  isZero := IsZero.of_full_of_faithful_of_isZero P.opEquivalence.inverse _ (isZero Wd P.op H)
  cof := Wd.cof.inverseImage P.ι.op
  weq := Wd.weq.inverseImage P.ι.op
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact Wd.cof_iso _ (inferInstance : IsIso (P.ι.op.map f))
  weq_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact Wd.weq_iso _ (inferInstance : IsIso (P.ι.op.map f))
  cof_zero X := by
    have hz : IsZero (P.ι.op.obj (op (⟨Wd.zero.unop, H.zero_mem⟩ : P.FullSubcategory))) := by
      simpa using Wd.isZero
    let e := hz.iso Wd.isZero
    change Wd.cof _
    have hh := Wd.cof.comp_mem e.hom (Wd.isZero.to_ (P.ι.op.obj X))
      (Wd.cof_iso _ (inferInstance : IsIso e.hom)) (Wd.cof_zero _)
    convert hh using 1
    exact hz.eq_of_src _ _
  pushout_exists i f hi := by
    obtain ⟨Q, g, j, h⟩ := (waldhausenStructure Wd P.op H).pushout_exists
      (P.opEquivalence.inverse.map i) (P.opEquivalence.inverse.map f) hi
    exact ⟨P.opEquivalence.functor.obj Q, P.opEquivalence.functor.map g,
      P.opEquivalence.functor.map j, h.map P.opEquivalence.functor⟩
  cof_pushout := by
    intro A B D Q i f g j hi h
    exact Wd.cof_pushout hi (inclusion_map_pushout Wd P.op H
      (i := P.opEquivalence.inverse.map i) hi (h.map P.opEquivalence.inverse))
  gluing := by
    intro A B D Q A' B' D' Q' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
    exact Wd.gluing (P.ι.op.map a) (P.ι.op.map b) (P.ι.op.map d) (P.ι.op.map p) hi hi'
      (inclusion_map_pushout Wd P.op H (i := P.opEquivalence.inverse.map i) hi (h.map
        P.opEquivalence.inverse))
      (inclusion_map_pushout Wd P.op H (i := P.opEquivalence.inverse.map i') hi' (h'.map
        P.opEquivalence.inverse))
      (congrArg P.ι.op.map ei) (congrArg P.ι.op.map ef)
      (congrArg P.ι.op.map eg) (congrArg P.ι.op.map ej) ha hb hd

/-- The original opposite inclusion preserves every actual cofibration pushout. -/
theorem opposite_inclusion_exact : IsExact (oppositeStructure Wd P H).cof
    (oppositeStructure Wd P H).weq Wd.cof Wd.weq P.ι.op where
  zero h := Wd.isZero.of_iso (P.ι.op.mapIso (h.iso (oppositeStructure Wd P H).isZero))
  cofibration _ h := h
  weak _ h := h
  pushout {_ _ _ _ i _ _ _} hi h := inclusion_map_pushout Wd P.op H (i :=
    P.opEquivalence.inverse.map i) hi (h.map P.opEquivalence.inverse)

/-- Genuine inherited forward and opposite structures retain the original
zero-square duality. Closure is used to preserve arbitrary chosen squares. -/
theorem opposite_compatible (W : Structure C) (h : IsCompatibleDual W Wd)
    (Hf : Closed W P) :
    IsCompatibleDual (waldhausenStructure W P Hf) (oppositeStructure Wd P H) where
  weak f := h.weak f.hom
  cofiber i z q s hZ := by
    have hz := (inclusion_exact W P Hf).zero hZ
    constructor
    · rintro ⟨hi, hp⟩
      obtain ⟨hq, hpb⟩ := (h.cofiber i.hom z.hom q.hom s.hom hz).mp
        ⟨hi, inclusion_map_pushout W P Hf hi hp⟩
      exact ⟨hq, IsPullback.of_map_of_faithful P.ι hpb⟩
    · rintro ⟨hq, hpb⟩
      have hp := (opposite_inclusion_exact Wd P H).pushout hq hpb.op.flip
      obtain ⟨hi, hpo⟩ := (h.cofiber i.hom z.hom q.hom s.hom hz).mpr
        ⟨hq, hp.unop.flip⟩
      exact ⟨hi, IsPushout.of_map_of_faithful P.ι hpo⟩

end CategoryTheory.Waldhausen.CofibrationClosedSubcategory
