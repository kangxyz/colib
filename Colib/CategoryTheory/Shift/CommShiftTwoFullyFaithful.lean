/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp

/-! # Reflection of the two signed shift comparisons along fully faithful functors -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor.CommShift₂

/-- A fully faithful additive functor reflects both signed shift comparisons of a bifunctor. -/
@[instance_reducible]
def ofFullyFaithfulInt {C₁ C₂ A A' : Type*} [Category* C₁] [Category* C₂]
    [Category* A] [Category* A'] [Preadditive A] [Preadditive A']
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift A ℤ] [HasShift A' ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor A' n).Additive]
    (V : A ⥤ A') [V.Full] [V.Faithful] [V.CommShift ℤ] [V.Additive]
    (G : C₁ ⥤ C₂ ⥤ A)
    [(G ⋙ (whiskeringRight C₂ A A').obj V).CommShift₂Int] : G.CommShift₂Int := by
  let T := G ⋙ (whiskeringRight C₂ A A').obj V
  let r (X : C₁) : (G.obj X).CommShift ℤ :=
    Functor.CommShift.ofComp (F := G.obj X) (G := V) (Iso.refl (T.obj X)) ℤ
  let l (Y : C₂) : (G.flip.obj Y).CommShift ℤ :=
    Functor.CommShift.ofComp (F := G.flip.obj Y) (G := V) (Iso.refl (T.flip.obj Y)) ℤ
  have hr (X : C₁) (Y : C₂) (n : ℤ) :
      let := r X
      ((T.obj X).commShiftIso n).hom.app Y =
        V.map (((G.obj X).commShiftIso n).hom.app Y) ≫
          (V.commShiftIso n).hom.app ((G.obj X).obj Y) := by
    let := r X
    let e : G.obj X ⋙ V ≅ T.obj X := Iso.refl _
    change _ = V.map ((Functor.CommShift.OfComp.iso e n).hom.app Y) ≫
      (V.commShiftIso n).hom.app ((G.obj X).obj Y)
    rw [Functor.CommShift.OfComp.map_iso_hom_app]
    simp only [e, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
      Category.assoc, Iso.inv_hom_id_app]
    let sh := shiftFunctor A' n
    let K := V.obj ((G.obj X).obj Y)
    change _ = ((T.obj X).commShiftIso n).hom.app Y ≫ sh.map (𝟙 K) ≫ 𝟙 (sh.obj K)
    have hi : sh.map (𝟙 K) ≫ 𝟙 (sh.obj K) = 𝟙 (sh.obj K) :=
      (Category.comp_id _).trans (sh.map_id K)
    exact ((congrArg (((T.obj X).commShiftIso n).hom.app Y ≫ ·) hi).trans
      (Category.comp_id _)).symm
  have hl (X : C₁) (Y : C₂) (n : ℤ) :
      let := l Y
      ((T.flip.obj Y).commShiftIso n).hom.app X =
        V.map (((G.flip.obj Y).commShiftIso n).hom.app X) ≫
          (V.commShiftIso n).hom.app ((G.obj X).obj Y) := by
    let := l Y
    let e : G.flip.obj Y ⋙ V ≅ T.flip.obj Y := Iso.refl _
    change _ = V.map ((Functor.CommShift.OfComp.iso e n).hom.app X) ≫
      (V.commShiftIso n).hom.app ((G.flip.obj Y).obj X)
    rw [Functor.CommShift.OfComp.map_iso_hom_app]
    simp only [e, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
      Category.assoc, Iso.inv_hom_id_app]
    let sh := shiftFunctor A' n
    let K := V.obj ((G.flip.obj Y).obj X)
    change _ = ((T.flip.obj Y).commShiftIso n).hom.app X ≫ sh.map (𝟙 K) ≫ 𝟙 (sh.obj K)
    have hi : sh.map (𝟙 K) ≫ 𝟙 (sh.obj K) = 𝟙 (sh.obj K) :=
      (Category.comp_id _).trans (sh.map_id K)
    exact ((congrArg (((T.flip.obj Y).commShiftIso n).hom.app X ≫ ·) hi).trans
      (Category.comp_id _)).symm
  refine
    { commShiftObj := r
      commShiftFlipObj := l
      commShift_map := fun {X X'} f => ?_
      commShift_flip_map := fun {Y Y'} g => ?_
      comm := fun X Y m n => ?_ }
  · let := r X
    let := r X'
    refine ⟨fun n => ?_⟩
    ext Y
    apply V.map_injective
    have h := NatTrans.shift_app_comm (T.map f) n Y
    rw [hr X Y n, hr X' Y n] at h
    change V.map (((G.obj X).commShiftIso n).hom.app Y ≫
        (shiftFunctor A n).map ((G.map f).app Y)) =
      V.map ((G.map f).app (Y⟦n⟧) ≫ ((G.obj X').commShiftIso n).hom.app Y)
    simp only [Functor.map_comp]
    apply (cancel_mono ((V.commShiftIso n).hom.app ((G.obj X').obj Y))).1
    erw [Category.assoc, Category.assoc, (V.commShiftIso n).hom.naturality]
    change (V.map (((G.obj X).commShiftIso n).hom.app Y) ≫ (V.commShiftIso n).hom.app
        ((G.obj X).obj Y)) ≫ (shiftFunctor A' n).map (V.map ((G.map f).app Y)) =
      V.map ((G.map f).app (Y⟦n⟧)) ≫ V.map (((G.obj X').commShiftIso n).hom.app Y) ≫
        (V.commShiftIso n).hom.app ((G.obj X').obj Y) at h
    exact (Category.assoc _ _ _).symm.trans h
  · let := l Y
    let := l Y'
    refine ⟨fun n => ?_⟩
    ext X
    apply V.map_injective
    have h := NatTrans.shift_app_comm (T.flip.map g) n X
    rw [hl X Y n, hl X Y' n] at h
    change V.map (((G.flip.obj Y).commShiftIso n).hom.app X ≫
        (shiftFunctor A n).map ((G.flip.map g).app X)) =
      V.map ((G.flip.map g).app (X⟦n⟧) ≫ ((G.flip.obj Y').commShiftIso n).hom.app X)
    simp only [Functor.map_comp]
    apply (cancel_mono ((V.commShiftIso n).hom.app ((G.obj X).obj Y'))).1
    erw [Category.assoc, Category.assoc, (V.commShiftIso n).hom.naturality]
    change (V.map (((G.flip.obj Y).commShiftIso n).hom.app X) ≫ (V.commShiftIso n).hom.app
        ((G.flip.obj Y).obj X)) ≫ (shiftFunctor A' n).map (V.map ((G.flip.map g).app X)) =
      V.map ((G.flip.map g).app (X⟦n⟧)) ≫
        V.map (((G.flip.obj Y').commShiftIso n).hom.app X) ≫
        (V.commShiftIso n).hom.app ((G.flip.obj Y').obj X) at h
    exact (Category.assoc _ _ _).symm.trans h
  · let := r X
    let := r (X⟦m⟧)
    let := l Y
    let := l (Y⟦n⟧)
    let Z := (G.obj X).obj Y
    let a := ((G.obj (X⟦m⟧)).commShiftIso n).hom.app Y
    let b := ((G.flip.obj Y).commShiftIso m).hom.app X
    let d := ((G.flip.obj (Y⟦n⟧)).commShiftIso m).hom.app X
    let f := ((G.obj X).commShiftIso n).hom.app Y
    let e := (V.commShiftIso n).hom.app (Z⟦m⟧) ≫ ((V.commShiftIso m).hom.app Z)⟦n⟧'
    let e' := (V.commShiftIso m).hom.app (Z⟦n⟧) ≫ ((V.commShiftIso n).hom.app Z)⟦m⟧'
    let z := ((CommShift₂Setup.int (D := A)).ε m n).val
    let z' := ((CommShift₂Setup.int (D := A')).ε m n).val
    let z₀ := z.app (Z⟦m⟧⟦n⟧)
    let j := (shiftComm Z m n).inv
    let j' := (shiftComm (V.obj Z) m n).inv
    have h := T.commShift₂_comm CommShift₂Setup.int X Y m n
    rw [hr (X⟦m⟧) Y n, hl X Y m, hl X (Y⟦n⟧) m, hr X Y n] at h
    change (V.map a ≫ (V.commShiftIso n).hom.app ((G.obj (X⟦m⟧)).obj Y)) ≫
        (V.map b ≫ (V.commShiftIso m).hom.app Z)⟦n⟧' =
      (V.map d ≫ (V.commShiftIso m).hom.app ((G.obj X).obj (Y⟦n⟧))) ≫
        (V.map f ≫ (V.commShiftIso n).hom.app Z)⟦m⟧' ≫ j' ≫
          z'.app ((V.obj Z)⟦m⟧⟦n⟧) at h
    simp only [Functor.map_comp, Category.assoc] at h
    have hbn (T : A') (u : (V.obj (Z⟦m⟧))⟦n⟧ ⟶ T) :=
      (V.commShiftIso n).hom.naturality_assoc b u
    have hfm (T : A') (u : (V.obj (Z⟦n⟧))⟦m⟧ ⟶ T) :=
      (V.commShiftIso m).hom.naturality_assoc f u
    change ∀ (T : A') (u : (V.obj (Z⟦m⟧))⟦n⟧ ⟶ T),
        V.map (b⟦n⟧') ≫ (V.commShiftIso n).hom.app (Z⟦m⟧) ≫ u =
        (V.commShiftIso n).hom.app ((G.obj (X⟦m⟧)).obj Y) ≫
          (shiftFunctor A' n).map (V.map b) ≫ u at hbn
    change ∀ (T : A') (u : (V.obj (Z⟦n⟧))⟦m⟧ ⟶ T),
        V.map (f⟦m⟧') ≫ (V.commShiftIso m).hom.app (Z⟦n⟧) ≫ u =
        (V.commShiftIso m).hom.app ((G.obj X).obj (Y⟦n⟧)) ≫
          (shiftFunctor A' m).map (V.map f) ≫ u at hfm
    rw [← hbn, ← hfm, ← V.map_comp_assoc, ← V.map_comp_assoc] at h
    have hε : V.map z₀ = z'.app (V.obj (Z⟦m⟧⟦n⟧)) := by
      change V.map (((CommShift₂Setup.int (D := A)).ε m n).val.app (Z⟦m⟧⟦n⟧)) =
        ((CommShift₂Setup.int (D := A')).ε m n).val.app (V.obj (Z⟦m⟧⟦n⟧))
      simp only [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow, Units.smul_def,
        Functor.map_zsmul, V.map_id]
    have hj : V.map j ≫ e = e' ≫ j' := by
      simpa only [e, e', j, j', Category.assoc] using Functor.map_shiftComm_inv V Z m n
    have he : V.map z₀ ≫ e = e ≫ z'.app ((V.obj Z)⟦m⟧⟦n⟧) :=
      hε ▸ (z'.naturality e).symm
    have : IsIso e := by dsimp [e]; infer_instance
    change a ≫ b⟦n⟧' = d ≫ f⟦m⟧' ≫ j ≫ z₀
    apply V.map_injective
    apply (cancel_mono e).1
    calc
      V.map (a ≫ b⟦n⟧') ≫ e =
          V.map (d ≫ f⟦m⟧') ≫ e' ≫ j' ≫ z'.app ((V.obj Z)⟦m⟧⟦n⟧) := by
        simpa only [e, e', Category.assoc] using h
      _ = V.map (d ≫ f⟦m⟧' ≫ j ≫ z₀) ≫ e := by
        rw [← Category.assoc e' j', ← hj, Category.assoc, ← he,
          ← V.map_comp_assoc, ← V.map_comp_assoc, Category.assoc, Category.assoc]

end CategoryTheory.Functor.CommShift₂
