/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Inclusion
public import Colib.CategoryTheory.Triangulated.Stabilization.Pretriangulated

/-! # Exactness of tensoring in stabilization

For a fixed stable tensor factor, its numerator tensors each finite
realization. The inverse associator moves one added twist to the end of
this tensor product. If this comparison commutes with the selected shifts,
the iterated comparisons identify the shifted connecting maps. Stable left
tensoring is then exact whenever ambient left tensoring by the numerator is
exact. The stable braiding transports this exact structure to right tensoring.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory Pretriangulated Limits CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (L : C)

local notation "T" => tensorRight L
local notation "I" => iterateTensorObj L
local notation "P" => iterateTensorIso L
local notation "S" => Stabilization (tensorRight L)

/-- Moving one right-hand twist past a fixed left tensor factor. -/
def tensorLeftTwistIso (A : C) : T ⋙ tensorLeft A ≅ tensorLeft A ⋙ T :=
  NatIso.ofComponents (fun X => (α_ A X L).symm) (by
    intro X Y f
    exact associator_inv_naturality_middle A f L)

private def iterateTensorLeftNatIso (A : C) : (n : ℕ) →
    iterate T n ⋙ tensorLeft A ≅ tensorLeft A ⋙ iterate T n
  | 0 => (tensorLeft A).leftUnitor ≪≫ (tensorLeft A).rightUnitor.symm
  | n + 1 =>
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (iterate T n) (tensorLeftTwistIso L A) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (iterateTensorLeftNatIso A n) T ≪≫
        Functor.associator _ _ _

section Braided

variable [BraidedCategory C]

private lemma iterateTensorLeftNatIso_app (A X : C) (n : ℕ) :
    (iterateTensorLeftNatIso L A n).app X =
      P A X 0 n ≪≫ eqToIso (congrArg (fun k => I k (A ⊗ X)) (Nat.zero_add n)) := by
  induction n with
  | zero =>
      have e : eqToIso (congrArg (fun k => I k (A ⊗ X)) (Nat.zero_add 0)) =
          Iso.refl (A ⊗ X) := eqToIso_refl _
      rw [e]
      apply Iso.ext
      change 𝟙 (A ⊗ X) ≫ 𝟙 (A ⊗ X) = 𝟙 (A ⊗ X) ≫ 𝟙 (A ⊗ X)
      rfl
  | succ n ih =>
      apply Iso.ext
      have e := congrArg Iso.hom ih
      change (iterateTensorLeftNatIso L A n).hom.app X = _ at e
      simp only [iterateTensorLeftNatIso, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
        Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
      erw [e]
      simp only [Iso.trans_hom, eqToIso.hom, Functor.map_comp, eqToHom_map]
      change 𝟙 (A ⊗ (I n X ⊗ L)) ≫
          ((moveTensorRight L A (I n X)).hom ≫ (P A X 0 n).hom ▷ L ≫ eqToHom _) =
        ((moveTensorRight L A (I n X)).hom ≫ (P A X 0 n).hom ▷ L) ≫ eqToHom _
      rw [Category.id_comp, Category.assoc]

end Braided

section Iterates

variable [HasShift C ℤ] [(tensorRight L).CommShift ℤ] (A : C) [(tensorLeft A).CommShift ℤ]

local notation "F" => tensorLeft A

private lemma iterateTensorLeftNatIso_commShift [NatTrans.CommShift (tensorLeftTwistIso L A).hom ℤ]
    (n : ℕ) : NatTrans.CommShift (iterateTensorLeftNatIso L A n).hom ℤ := by
  induction n with
  | zero =>
      change NatTrans.CommShift
        ((F).leftUnitor.hom ≫ (F).rightUnitor.inv) ℤ
      infer_instance
  | succ n ih =>
      let := ih
      change NatTrans.CommShift
        ((Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (iterate T n) (tensorLeftTwistIso L A).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (iterateTensorLeftNatIso L A n).hom T ≫
          (Functor.associator _ _ _).hom) ℤ
      infer_instance

private lemma iterateTensorLeftNatIso_shift [NatTrans.CommShift (tensorLeftTwistIso L A).hom ℤ]
    (n : ℕ) (r : ℤ) (X : C) :
    (A ◁ ((iterate T n).commShiftIso r).hom.app X) ≫ ((F).commShiftIso r).hom.app (I n X) ≫
      ((iterateTensorLeftNatIso L A n).hom.app X)⟦r⟧' =
    (iterateTensorLeftNatIso L A n).hom.app (X⟦r⟧) ≫
      (iterate T n).map (((F).commShiftIso r).hom.app X) ≫
        ((iterate T n).commShiftIso r).hom.app (A ⊗ X) := by
  let := iterateTensorLeftNatIso_commShift L A n
  have e := NatTrans.shift_app_comm (iterateTensorLeftNatIso L A n).hom r X
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at e
  exact e

end Iterates

section Numerator

variable [(tensorRight L).Full] [(tensorRight L).Faithful]

private lemma homEquiv_numeratorHom {X Y : S} (h : X.level = Y.level) (f : X.obj ⟶ Y.obj)
    (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    homEquiv T X Y n hX hY (numeratorHom L h f) =
      (iterate T (n - X.level)).map f ≫
        eqToHom (congrArg (fun k => I k Y.obj) (by rw [h] : n - X.level = n - Y.level)) := by
  obtain ⟨A, a⟩ := X
  obtain ⟨B, b⟩ := Y
  change a = b at h
  subst b
  have hf : numeratorHom L (X := ⟨A, a⟩) (Y := ⟨B, a⟩) rfl f = (atLevel T a).map f := by
    exact numeratorHom_atLevel L a f
  rw [hf]
  change homEquiv T ((atLevel T a).obj A) ((atLevel T a).obj B) n hX hY
      ((atLevel T a).map f) = (iterate T (n - a)).map f ≫ 𝟙 _
  rw [homEquiv_atLevel_map_of_le T a n hX, Category.comp_id]

end Numerator

section TensorLeft

variable [BraidedCategory C] [(tensorRight L).Full] [(tensorRight L).Faithful]
  [HasShift C ℤ] [(tensorRight L).CommShift ℤ]
variable (B : Stabilization (tensorRight L)) [(tensorLeft B.obj).CommShift ℤ]

local notation "F" => tensorLeft B.obj
local infixr:70 " ⊗ₛ " => tensorObj L
local infixr:70 " ⊗ₛₘ " => tensorHom L

/-- Left tensoring by a numerator realizes the stable tensor at the sum of levels. -/
def stageTensorLeftIso (X : S) (n : ℕ) (hx : X.level ≤ n) :
    B.obj ⊗ stage T X n ≅ stage T (B ⊗ₛ X) (B.level + n) :=
  whiskerRightIso (stageCoordinateIso L B (Nat.add_zero B.level)).symm (stage T X n) ≪≫
    stageTensorIso L B X (Nat.le_refl _) hx

omit [(tensorRight L).Full] [(tensorRight L).Faithful] [HasShift C ℤ]
  [(tensorRight L).CommShift ℤ] [(tensorLeft B.obj).CommShift ℤ] in
private lemma stageTensorLeftIso_iter (X : S) (n : ℕ) (hx : X.level ≤ n) :
    stageTensorLeftIso L B X n hx =
      (iterateTensorLeftNatIso L B.obj (n - X.level)).app X.obj ≪≫
        (stageCoordinateIso L (B ⊗ₛ X)
          (show (B ⊗ₛ X).level + (n - X.level) = B.level + n by
            rw [level_tensorObj, Nat.add_assoc, Nat.add_sub_of_le hx])).symm := by
  rw [iterateTensorLeftNatIso_app]
  let q := n - X.level
  let s := (B.level + n) - (B ⊗ₛ X).level
  have eqs : s = q := by dsimp [s, q]; omega
  have h (p : ℕ) (hp : p = 0) :
      (whiskerRightIso (eqToIso (congrArg (fun k => I k B.obj) hp)).symm (I q X.obj) ≪≫
        (P B.obj X.obj p q ≪≫
          eqToIso (congrArg (fun k => I k (B.obj ⊗ X.obj)) (by omega : p + q = s)))) =
      (P B.obj X.obj 0 q ≪≫
        eqToIso (congrArg (fun k => I k (B.obj ⊗ X.obj)) (Nat.zero_add q))) ≪≫
          eqToIso (congrArg (fun k => I k (B.obj ⊗ X.obj)) eqs.symm) := by
    subst p
    apply Iso.ext
    simp only [eqToIso_refl, Iso.refl_symm, whiskerRightIso_refl, Iso.trans_hom, Iso.refl_hom,
      Category.id_comp, Category.assoc, eqToIso.hom, eqToHom_trans]
  exact h (B.level - B.level) (Nat.sub_self B.level)

omit [HasShift C ℤ] [(tensorRight L).CommShift ℤ] [(tensorLeft B.obj).CommShift ℤ] in
/-- The left tensor stage comparison intertwines the realized tensor map. -/
lemma stageTensorLeftIso_natural (hL : (β_ L L).hom = 𝟙 _)
    {X Y : S} (f : X ⟶ Y) (n : ℕ) (hx : X.level ≤ n) (hy : Y.level ≤ n) :
    (F).map (homEquiv T X Y n hx hy f) ≫ (stageTensorLeftIso L B Y n hy).hom =
      (stageTensorLeftIso L B X n hx).hom ≫
        homEquiv T (B ⊗ₛ X) (B ⊗ₛ Y) (B.level + n)
          (Nat.add_le_add_left hx B.level) (Nat.add_le_add_left hy B.level) (𝟙 B ⊗ₛₘ f) := by
  rw [homEquiv_tensorHom L hL _ f (Nat.le_refl _) (Nat.le_refl _) hx hy, homEquiv_id]
  simp only [stageTensorLeftIso, tensorStageHom, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, whiskerRightIso_hom, Iso.symm_hom, id_tensorHom]
  exact whisker_exchange_assoc (stageCoordinateIso L B (Nat.add_zero B.level)).inv
    (homEquiv T X Y n hx hy f) (stageTensorIso L B Y (Nat.le_refl _) hy).hom

/-- The commutation with shift of stable left tensor at the numerator. -/
def tensorLeftShiftApp (X : S) (r : ℤ) : (B ⊗ₛ X⟦r⟧) ≅ (B ⊗ₛ X)⟦r⟧ :=
  numeratorIso L (show (B ⊗ₛ X⟦r⟧).level = ((B ⊗ₛ X)⟦r⟧).level from rfl)
    (((F).commShiftIso r).app X.obj)

/-- The left tensor stage comparison intertwines the shift comparison. -/
lemma stageTensorLeftIso_shift [NatTrans.CommShift (tensorLeftTwistIso L B.obj).hom ℤ]
    (X : S) (r : ℤ) (n : ℕ) (hx : X.level ≤ n) :
    (stageTensorLeftIso L B (X⟦r⟧) n hx).hom ≫
      homEquiv T (B ⊗ₛ X⟦r⟧) ((B ⊗ₛ X)⟦r⟧) (B.level + n)
        (Nat.add_le_add_left hx B.level) (Nat.add_le_add_left hx B.level)
        (tensorLeftShiftApp L B X r).hom ≫
      (stageShiftIso T r (B ⊗ₛ X) (B.level + n)).hom =
    (F).map (stageShiftIso T r X n).hom ≫ ((F).commShiftIso r).hom.app (stage T X n) ≫
      ((stageTensorLeftIso L B X n hx).hom)⟦r⟧' := by
  let U := B ⊗ₛ X⟦r⟧
  let V := (B ⊗ₛ X)⟦r⟧
  let k := B.level + n
  have huv : U.level = V.level := rfl
  let d : U.obj ⟶ V.obj := ((F).commShiftIso r).hom.app X.obj
  have hu : U.level ≤ k := Nat.add_le_add_left hx _
  have hv : V.level ≤ k := Nat.add_le_add_left hx _
  have e : homEquiv T U V k hu hv (tensorLeftShiftApp L B X r).hom =
      (iterate T (k - V.level)).map d := by
    change homEquiv T U V k hu hv (numeratorHom L huv d) = _
    rw [homEquiv_numeratorHom L huv d]
    exact Category.comp_id _
  rw [stageTensorLeftIso_iter L B (X⟦r⟧) n hx, stageTensorLeftIso_iter L B X n hx]
  change _ ≫ homEquiv T U V k hu hv (tensorLeftShiftApp L B X r).hom ≫ _ = _
  rw [e]
  let q := n - X.level
  let p := k - V.level
  have h : p = q := by dsimp [p, q, k, V]; omega
  have hp (j : ℕ) (hj : j = q) :
      (iterateTensorLeftNatIso L B.obj q).hom.app (X.obj⟦r⟧) ≫
        eqToHom (congrArg (fun t => I t U.obj) hj.symm) ≫
        (iterate T j).map d ≫ ((iterate T j).commShiftIso r).hom.app (B.obj ⊗ X.obj) =
      (F).map (((iterate T q).commShiftIso r).hom.app X.obj) ≫
        ((F).commShiftIso r).hom.app (I q X.obj) ≫
          ((iterateTensorLeftNatIso L B.obj q).hom.app X.obj ≫
            eqToHom (congrArg (fun t => I t (B.obj ⊗ X.obj)) hj.symm))⟦r⟧' := by
    subst j
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (iterateTensorLeftNatIso_shift L B.obj q r X.obj).symm
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, stageCoordinateIso, eqToIso.inv,
    Category.assoc]
  exact hp p h

variable [NatTrans.CommShift (tensorLeftTwistIso L B.obj).hom ℤ]

/-- The numerator comparison is natural on stable maps. -/
lemma tensorLeftShiftApp_natural (hL : (β_ L L).hom = 𝟙 _) {X Y : S}
    (f : X ⟶ Y) (r : ℤ) :
    (𝟙 B ⊗ₛₘ f⟦r⟧') ≫ (tensorLeftShiftApp L B Y r).hom =
      (tensorLeftShiftApp L B X r).hom ≫ (𝟙 B ⊗ₛₘ f)⟦r⟧' := by
  let n := max X.level Y.level
  have hx : X.level ≤ n := Nat.le_max_left _ _
  have hy : Y.level ≤ n := Nat.le_max_right _ _
  let k := B.level + n
  have hBX : (B ⊗ₛ X).level ≤ k := Nat.add_le_add_left hx _
  have hBY : (B ⊗ₛ Y).level ≤ k := Nat.add_le_add_left hy _
  let a := stageTensorLeftIso L B X n hx
  let b := stageTensorLeftIso L B Y n hy
  let ar := stageTensorLeftIso L B (X⟦r⟧) n hx
  let br := stageTensorLeftIso L B (Y⟦r⟧) n hy
  let u := homEquiv T X Y n hx hy f
  let ur := homEquiv T (X⟦r⟧) (Y⟦r⟧) n hx hy (f⟦r⟧')
  let v := homEquiv T (B ⊗ₛ X) (B ⊗ₛ Y) k hBX hBY (𝟙 B ⊗ₛₘ f)
  let vr := homEquiv T (B ⊗ₛ X⟦r⟧) (B ⊗ₛ Y⟦r⟧) k hBX hBY (𝟙 B ⊗ₛₘ f⟦r⟧')
  let cX := homEquiv T (B ⊗ₛ X⟦r⟧) ((B ⊗ₛ X)⟦r⟧) k hBX hBX
    (tensorLeftShiftApp L B X r).hom
  let cY := homEquiv T (B ⊗ₛ Y⟦r⟧) ((B ⊗ₛ Y)⟦r⟧) k hBY hBY
    (tensorLeftShiftApp L B Y r).hom
  let dX := (stageShiftIso T r X n).hom
  let dY := (stageShiftIso T r Y n).hom
  let Dₓ := stageShiftIso T r (B ⊗ₛ X) k
  let Dᵧ := stageShiftIso T r (B ⊗ₛ Y) k
  let gX := ((F).commShiftIso r).hom.app (stage T X n)
  let gY := ((F).commShiftIso r).hom.app (stage T Y n)
  have eX : ar.hom ≫ cX ≫ Dₓ.hom = (F).map dX ≫ gX ≫ a.hom⟦r⟧' :=
    stageTensorLeftIso_shift L B X r n hx
  have eY : br.hom ≫ cY ≫ Dᵧ.hom = (F).map dY ≫ gY ≫ b.hom⟦r⟧' :=
    stageTensorLeftIso_shift L B Y r n hy
  have e : (F).map u ≫ b.hom = a.hom ≫ v := stageTensorLeftIso_natural L B hL f n hx hy
  have er : (F).map ur ≫ br.hom = ar.hom ≫ vr :=
    stageTensorLeftIso_natural L B hL (f⟦r⟧') n hx hy
  have hs : ur ≫ dY = dX ≫ u⟦r⟧' := by
    dsimp only [ur, dY, dX, u]
    rw [homEquiv_shift T r f n hx hy]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hNat : (F).map (u⟦r⟧') ≫ gY = gX ≫ ((F).map u)⟦r⟧' :=
    (F).commShiftIso_hom_naturality u r
  apply hom_ext T (X := B ⊗ₛ X⟦r⟧) (Y := (B ⊗ₛ Y)⟦r⟧) k hBX hBY
  rw [homEquiv_comp T (𝟙 B ⊗ₛₘ f⟦r⟧') (tensorLeftShiftApp L B Y r).hom k hBX hBY hBY,
    homEquiv_comp T (tensorLeftShiftApp L B X r).hom ((𝟙 B ⊗ₛₘ f)⟦r⟧') k hBX hBX hBY,
    homEquiv_shift T r (𝟙 B ⊗ₛₘ f) k hBX hBY]
  change vr ≫ cY = cX ≫ Dₓ.hom ≫ v⟦r⟧' ≫ Dᵧ.inv
  apply (cancel_epi ar.hom).1
  apply (cancel_mono Dᵧ.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← reassoc_of% er, eY, ← Functor.map_comp_assoc, hs, Functor.map_comp_assoc,
    reassoc_of% hNat, reassoc_of% eX]
  rw [← Functor.map_comp, e, Functor.map_comp]

/-- Shift commutation for the stable functor of tensoring on the left. -/
@[instance_reducible]
def stableTensorLeftCommShift (hL : (β_ L L).hom = 𝟙 _) :
    letI := monoidalCategory L hL
    (tensorLeft B).CommShift ℤ :=
  letI := monoidalCategory L hL
  { commShiftIso := fun r => NatIso.ofComponents (fun X => tensorLeftShiftApp L B X r)
      (fun f => tensorLeftShiftApp_natural L B hL f r)
    commShiftIso_zero := by
      ext X
      rw [Functor.CommShift.isoZero_hom_app]
      let n := B.level + X.level
      let t : (B ⊗ₛ X⟦(0 : ℤ)⟧).obj ⟶ (B ⊗ₛ X).obj := by
        exact (F).map ((shiftFunctorZero C ℤ).hom.app X.obj)
      let u : (B ⊗ₛ X).obj ⟶ ((B ⊗ₛ X)⟦(0 : ℤ)⟧).obj :=
        (shiftFunctorZero C ℤ).inv.app (B.obj ⊗ X.obj)
      have h₁ : (B ⊗ₛ X⟦(0 : ℤ)⟧).level = (B ⊗ₛ X).level := rfl
      have h₂ : (B ⊗ₛ X).level = ((B ⊗ₛ X)⟦(0 : ℤ)⟧).level := rfl
      change (tensorLeftShiftApp L B X 0).hom =
        (𝟙 B ⊗ₛₘ (atLevel T X.level).map ((shiftFunctorZero C ℤ).hom.app X.obj)) ≫
          (atLevel T n).map ((shiftFunctorZero C ℤ).inv.app (B.obj ⊗ X.obj))
      let z : (X⟦(0 : ℤ)⟧).obj ⟶ X.obj := (shiftFunctorZero C ℤ).hom.app X.obj
      have hz : numeratorHom L (X := X⟦(0 : ℤ)⟧) (Y := X)
          (shift_obj_level T 0 X) z =
          (atLevel T X.level).map ((shiftFunctorZero C ℤ).hom.app X.obj) :=
        numeratorHom_atLevel L X.level _
      have hu : numeratorHom L h₂ u =
          (atLevel T n).map ((shiftFunctorZero C ℤ).inv.app (B.obj ⊗ X.obj)) :=
        numeratorHom_atLevel L n _
      rw [← hz, ← hu, ← numeratorHom_id L B, numeratorHom_tensorHom L hL, numeratorHom_comp]
      have he : ((F).commShiftIso (0 : ℤ)).hom.app X.obj = t ≫ u := by
        rw [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
        rfl
      have ht : (𝟙 B.obj ⊗ₘ z) = t := id_tensorHom _ _
      exact congrArg (numeratorHom L (h₁.trans h₂)) (he.trans
        (congrArg (fun f => f ≫ u) ht.symm))
    commShiftIso_add r s := by
      ext X
      rw [Functor.CommShift.isoAdd_hom_app]
      let n := B.level + X.level
      let X₀ := X⟦r + s⟧
      let X₁ := (X⟦r⟧)⟦s⟧
      let Y₀ := B ⊗ₛ X₀
      let Y₁ := B ⊗ₛ X₁
      let Y₂ := (B ⊗ₛ X⟦r⟧)⟦s⟧
      let Y₃ := ((B ⊗ₛ X)⟦r⟧)⟦s⟧
      let Y₄ := (B ⊗ₛ X)⟦r + s⟧
      let z : X₀.obj ⟶ X₁.obj := (shiftFunctorAdd C r s).hom.app X.obj
      let u : Y₃.obj ⟶ Y₄.obj := (shiftFunctorAdd C r s).inv.app (B.obj ⊗ X.obj)
      have h₁ : Y₀.level = Y₁.level := rfl
      have h₂ : Y₁.level = Y₂.level := rfl
      have h₃ : Y₂.level = Y₃.level := rfl
      have h₄ : Y₃.level = Y₄.level := rfl
      change (tensorLeftShiftApp L B X (r + s)).hom =
        (𝟙 B ⊗ₛₘ (atLevel T X.level).map z) ≫ (tensorLeftShiftApp L B (X⟦r⟧) s).hom ≫
          ((tensorLeftShiftApp L B X r).hom)⟦s⟧' ≫ (atLevel T n).map u
      have hz : numeratorHom L (X := X₀) (Y := X₁) rfl z = (atLevel T X.level).map z :=
        numeratorHom_atLevel L X.level _
      have hu : numeratorHom L h₄ u = (atLevel T n).map u := numeratorHom_atLevel L n _
      let v : (B ⊗ₛ X⟦r⟧).obj ⟶ ((B ⊗ₛ X)⟦r⟧).obj :=
        ((F).commShiftIso r).hom.app X.obj
      have hv : (tensorLeftShiftApp L B X r).hom = (atLevel T n).map v :=
        numeratorHom_atLevel L n _
      have hv' : ((tensorLeftShiftApp L B X r).hom)⟦s⟧' = (atLevel T n).map (v⟦s⟧') := by
        rw [hv]
        exact shift_map_atLevel T s n v
      have hv'' : numeratorHom L h₃ (v⟦s⟧') = (atLevel T n).map (v⟦s⟧') :=
        numeratorHom_atLevel L n _
      rw [← hz, ← hu, hv', ← hv'', ← numeratorHom_id L B, numeratorHom_tensorHom L hL]
      let w : Y₁.obj ⟶ Y₂.obj := ((F).commShiftIso s).hom.app (X.obj⟦r⟧)
      change numeratorHom L (h₁.trans (h₂.trans (h₃.trans h₄)))
          (((F).commShiftIso (r + s)).hom.app X.obj) =
        numeratorHom L h₁ (𝟙 B.obj ⊗ₘ z) ≫ numeratorHom L h₂ w ≫
          numeratorHom L h₃ (v⟦s⟧') ≫ numeratorHom L h₄ u
      rw [numeratorHom_comp, numeratorHom_comp, numeratorHom_comp]
      have he : ((F).commShiftIso (r + s)).hom.app X.obj =
          (F).map z ≫ w ≫ (v⟦s⟧') ≫ u := by
        rw [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
        rfl
      have ht : 𝟙 B.obj ⊗ₘ z = (F).map z := id_tensorHom _ _
      exact congrArg (numeratorHom L (h₁.trans (h₂.trans (h₃.trans h₄)))) (he.trans
        (congrArg (fun f => f ≫ w ≫ (v⟦s⟧') ≫ u) ht.symm)) }

section Triangles

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [(tensorRight L).IsTriangulated]
variable (hL : (β_ L L).hom = 𝟙 _)

include hL

/-- At finite stages, left tensoring induces the ambient tensor functor on triangles. -/
def stageTensorLeftTriangleIso (Δ : Triangle S) (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n) :
    letI := monoidalCategory L hL
    letI := stableTensorLeftCommShift L B hL
    (F).mapTriangle.obj (stageTriangle T Δ n h₁ h₂ h₃) ≅
      stageTriangle T ((tensorLeft B).mapTriangle.obj Δ) (B.level + n)
        (Nat.add_le_add_left h₁ _) (Nat.add_le_add_left h₂ _) (Nat.add_le_add_left h₃ _) := by
  letI := monoidalCategory L hL
  letI := stableTensorLeftCommShift L B hL
  refine Triangle.isoMk _ _ (stageTensorLeftIso L B Δ.obj₁ n h₁)
    (stageTensorLeftIso L B Δ.obj₂ n h₂) (stageTensorLeftIso L B Δ.obj₃ n h₃) ?_ ?_ ?_
  · exact stageTensorLeftIso_natural L B hL Δ.mor₁ n h₁ h₂
  · exact stageTensorLeftIso_natural L B hL Δ.mor₂ n h₂ h₃
  · let k := B.level + n
    have hB₁ : (B ⊗ₛ Δ.obj₁).level ≤ k := Nat.add_le_add_left h₁ _
    have hB₃ : (B ⊗ₛ Δ.obj₃).level ≤ k := Nat.add_le_add_left h₃ _
    let u := homEquiv T Δ.obj₃ (Δ.obj₁⟦(1 : ℤ)⟧) n h₃ h₁ Δ.mor₃
    let c := (tensorLeftShiftApp L B Δ.obj₁ 1).hom
    let v := 𝟙 B ⊗ₛₘ Δ.mor₃
    let a := stageTensorLeftIso L B Δ.obj₁ n h₁
    let ar := stageTensorLeftIso L B (Δ.obj₁⟦(1 : ℤ)⟧) n h₁
    let b := stageTensorLeftIso L B Δ.obj₃ n h₃
    change ((F).map (u ≫ (stageShiftIso T 1 Δ.obj₁ n).hom) ≫
        ((F).commShiftIso (1 : ℤ)).hom.app (stage T Δ.obj₁ n)) ≫ a.hom⟦(1 : ℤ)⟧' =
      b.hom ≫ homEquiv T (B ⊗ₛ Δ.obj₃) ((B ⊗ₛ Δ.obj₁)⟦(1 : ℤ)⟧) k hB₃ hB₁ (v ≫ c) ≫
        (stageShiftIso T 1 (B ⊗ₛ Δ.obj₁) k).hom
    rw [homEquiv_comp T v c k hB₃ hB₁ hB₁, Functor.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% (stageTensorLeftIso_natural L B hL Δ.mor₃ n h₃ h₁)]
    change _ = (F).map u ≫ ar.hom ≫ _ ≫ _
    rw [stageTensorLeftIso_shift L B Δ.obj₁ 1 n h₁]

/-- Left tensoring on the stabilization preserves distinguished triangles. -/
theorem stableTensorLeft_isTriangulated [(tensorLeft B.obj).IsTriangulated] :
    letI := monoidalCategory L hL
    letI := stableTensorLeftCommShift L B hL
    (tensorLeft B).IsTriangulated := by
  let := monoidalCategory L hL
  let := stableTensorLeftCommShift L B hL
  refine ⟨fun Δ hΔ => ?_⟩
  obtain ⟨n, h₁, h₂, h₃, h⟩ := hΔ
  exact ⟨B.level + n, Nat.add_le_add_left h₁ _, Nat.add_le_add_left h₂ _,
    Nat.add_le_add_left h₃ _, (distinguished_iff_of_iso
      (stageTensorLeftTriangleIso L B hL Δ n h₁ h₂ h₃)).1 ((F).map_distinguished _ h)⟩

end Triangles

end TensorLeft

section TensorRight

variable [SymmetricCategory C] [(tensorRight L).Full] [(tensorRight L).Faithful]
  [HasShift C ℤ] [(tensorRight L).CommShift ℤ]
variable (B : Stabilization (tensorRight L)) [(tensorLeft B.obj).CommShift ℤ]
  [NatTrans.CommShift (tensorLeftTwistIso L B.obj).hom ℤ]
variable (hL : (β_ L L).hom = 𝟙 _)

/-- Shift commutation on the right, induced by the braiding from stable left tensoring. -/
@[instance_reducible]
def stableTensorRightCommShift :
    letI := monoidalCategory L hL
    letI := symmetricCategory L hL
    (tensorRight B).CommShift ℤ := by
  letI := monoidalCategory L hL
  letI := symmetricCategory L hL
  letI := stableTensorLeftCommShift L B hL
  exact Functor.CommShift.ofIso (tensorLeftIsoTensorRight B) ℤ

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [(tensorRight L).IsTriangulated]

/-- Right tensoring on the stabilization preserves distinguished triangles. -/
theorem stableTensorRight_isTriangulated [(tensorLeft B.obj).IsTriangulated] :
    letI := monoidalCategory L hL
    letI := symmetricCategory L hL
    letI := stableTensorRightCommShift L B hL
    (tensorRight B).IsTriangulated := by
  let := monoidalCategory L hL
  let := symmetricCategory L hL
  let := stableTensorLeftCommShift L B hL
  let := stableTensorRightCommShift L B hL
  let := stableTensorLeft_isTriangulated L B hL
  let := Functor.CommShift.ofIso_compatibility (tensorLeftIsoTensorRight B) ℤ
  exact Functor.isTriangulated_of_iso (tensorLeftIsoTensorRight B)

end TensorRight

end CategoryTheory.Stabilization
