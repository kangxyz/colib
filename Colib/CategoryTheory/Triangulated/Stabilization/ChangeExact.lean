/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.ChangeFunctor
public import Colib.CategoryTheory.Triangulated.Stabilization.Pretriangulated

/-!
# Exactness of change of the stabilizing endofunctor

A shift-compatible natural isomorphism of endofunctors induces an exact
change functor. The shift comparison is the identity on each shifted
numerator, and the triangle comparison is the given isomorphism of iterates
on all three vertices at a common stage.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] {T U : C ⥤ C} (e : T ≅ U)
  [HasShift C ℤ] [T.CommShift ℤ] [U.CommShift ℤ] [NatTrans.CommShift e.hom ℤ]

set_option backward.isDefEq.respectTransparency false in
instance iterateChangeIso_commShift (n : ℕ) :
    NatTrans.CommShift (iterateChangeIso e n).hom ℤ := by
  induction n with
  | zero =>
    change NatTrans.CommShift (𝟙 (𝟭 C)) ℤ
    infer_instance
  | succ n ih =>
    let := ih
    change NatTrans.CommShift (Functor.whiskerRight (iterateChangeIso e n).hom T ≫
      Functor.whiskerLeft (iterate U n) e.hom) ℤ
    infer_instance

/-- Change of the transition commutes with the shift comparison at a common stage. -/
@[reassoc]
theorem stageChangeIso_shift_hom (r : ℤ) (X : Stabilization T) (n : ℕ) :
    (stageShiftIso T r X n).hom ≫ (stageChangeIso e X n).hom⟦r⟧' =
      (stageChangeIso e (shiftObj T r X) n).hom ≫
        (stageShiftIso U r (changeObj (U := U) X) n).hom :=
  NatTrans.shift_app_comm (iterateChangeIso e (n - X.level)).hom r X.obj

variable [T.Full] [T.Faithful] [U.Full] [U.Faithful]

set_option backward.isDefEq.respectTransparency false in
/-- The change functor sends the shifted morphism to the shift of its image. -/
theorem changeFunctor_shift_map (r : ℤ) {X Y : Stabilization T} (f : X ⟶ Y) :
    (changeFunctor e).map (f⟦r⟧') = ((changeFunctor e).map f)⟦r⟧' := by
  let n := max X.level Y.level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have hY : Y.level ≤ n := Nat.le_max_right _ _
  apply hom_ext U (X := changeObj (shiftObj T r X)) (Y := changeObj (shiftObj T r Y)) n hX hY
  change homEquiv U _ _ n hX hY (changeHomEquiv e _ _ (f⟦r⟧')) =
    homEquiv U ((changeObj (U := U) X)⟦r⟧) ((changeObj (U := U) Y)⟦r⟧) n hX hY
      (((changeFunctor e).map f)⟦r⟧')
  erw [homEquiv_changeHomEquiv e (f⟦r⟧') n hX hY, homEquiv_shift T r f n hX hY,
    homEquiv_shift U r ((changeFunctor e).map f) n hX hY]
  change _ = _ ≫ (homEquiv U _ _ n hX hY (changeHomEquiv e _ _ f))⟦r⟧' ≫ _
  erw [homEquiv_changeHomEquiv e f n hX hY]
  simp only [Iso.homCongr_apply, Functor.map_comp, Category.assoc]
  have hX' := stageChangeIso_shift_hom e r X n
  have hY' := stageChangeIso_shift_hom e r Y n
  have hXinv : (stageChangeIso e (shiftObj T r X) n).inv ≫ (stageShiftIso T r X n).hom =
      (stageShiftIso U r (changeObj (U := U) X) n).hom ≫
        (stageChangeIso e X n).inv⟦r⟧' := by
    apply (cancel_mono ((stageChangeIso e X n).hom⟦r⟧')).1
    rw [Category.assoc, hX', Iso.inv_hom_id_assoc, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]
  have hYinv : (stageShiftIso T r Y n).inv ≫ (stageChangeIso e (shiftObj T r Y) n).hom =
      (stageChangeIso e Y n).hom⟦r⟧' ≫ (stageShiftIso U r (changeObj (U := U) Y) n).inv := by
    apply (cancel_mono (stageShiftIso U r (changeObj (U := U) Y) n).hom).1
    rw [Category.assoc, ← hY', Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  erw [reassoc_of% hXinv, hYinv]
  rfl

/-- The shift comparison for change of endofunctor is the identity on objects. -/
def changeFunctorCommShiftIso (r : ℤ) :
    shiftFunctor (Stabilization T) r ⋙ changeFunctor e ≅
      changeFunctor e ⋙ shiftFunctor (Stabilization U) r :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change (changeFunctor e).map (f⟦r⟧') ≫ 𝟙 _ = 𝟙 _ ≫ ((changeFunctor e).map f)⟦r⟧'
    rw [Category.comp_id, Category.id_comp, changeFunctor_shift_map])

set_option backward.isDefEq.respectTransparency false in
instance changeFunctorCommShift : (changeFunctor e).CommShift ℤ where
  commShiftIso := changeFunctorCommShiftIso e
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app]
    change 𝟙 ((atLevel U X.level).obj (X.obj⟦(0 : ℤ)⟧)) =
      (changeFunctor e).map ((atLevel T X.level).map ((shiftFunctorZero C ℤ).hom.app X.obj)) ≫
        (atLevel U X.level).map ((shiftFunctorZero C ℤ).inv.app X.obj)
    rw [changeFunctor_map_atLevel, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  commShiftIso_add r s := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app]
    let n := X.level
    change 𝟙 ((atLevel U n).obj (X.obj⟦r + s⟧)) =
      (changeFunctor e).map ((atLevel T n).map ((shiftFunctorAdd C r s).hom.app X.obj)) ≫
        𝟙 ((atLevel U n).obj ((X.obj⟦r⟧)⟦s⟧)) ≫
          (shift U s).map (𝟙 ((atLevel U n).obj (X.obj⟦r⟧))) ≫
            (atLevel U n).map ((shiftFunctorAdd C r s).inv.app X.obj)
    have h : (shift U s).map (𝟙 ((atLevel U n).obj (X.obj⟦r⟧))) =
        𝟙 ((atLevel U n).obj ((X.obj⟦r⟧)⟦s⟧)) := (shift U s).map_id _
    erw [changeFunctor_map_atLevel, h, Category.id_comp, Category.id_comp, ← Functor.map_comp,
      Iso.hom_inv_id_app, Functor.map_id]

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [T.IsTriangulated] [U.IsTriangulated]

set_option backward.isDefEq.respectTransparency false in
/-- The realized image triangle is identified at the same stage by the three
original isomorphisms of iterates. -/
def changeFunctorStageTriangleIso (Δ : Triangle (Stabilization T)) (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n) :
    stageTriangle T Δ n h₁ h₂ h₃ ≅
      stageTriangle U ((changeFunctor e).mapTriangle.obj Δ) n h₁ h₂ h₃ :=
  Triangle.isoMk _ _ (stageChangeIso e Δ.obj₁ n) (stageChangeIso e Δ.obj₂ n)
    (stageChangeIso e Δ.obj₃ n)
    (by
      change _ = _ ≫ homEquiv U _ _ n h₁ h₂ (changeHomEquiv e _ _ Δ.mor₁)
      rw [homEquiv_changeHomEquiv e Δ.mor₁ n h₁ h₂]
      simp [stageTriangle])
    (by
      change _ = _ ≫ homEquiv U _ _ n h₂ h₃ (changeHomEquiv e _ _ Δ.mor₂)
      rw [homEquiv_changeHomEquiv e Δ.mor₂ n h₂ h₃]
      simp [stageTriangle])
    (by
      change (homEquiv T Δ.obj₃ (Δ.obj₁⟦(1 : ℤ)⟧) n h₃ h₁ Δ.mor₃ ≫
          (stageShiftIso T 1 Δ.obj₁ n).hom) ≫ (stageChangeIso e Δ.obj₁ n).hom⟦(1 : ℤ)⟧' =
        (stageChangeIso e Δ.obj₃ n).hom ≫
          homEquiv U (changeObj Δ.obj₃) (changeObj (Δ.obj₁⟦(1 : ℤ)⟧)) n h₃ h₁
            (changeHomEquiv e _ _ Δ.mor₃ ≫ 𝟙 _) ≫
            (stageShiftIso U 1 (changeObj (U := U) Δ.obj₁) n).hom
      erw [Category.comp_id, homEquiv_changeHomEquiv e Δ.mor₃ n h₃ h₁]
      simp only [Iso.homCongr_apply, Category.assoc, Iso.hom_inv_id_assoc,
        stageChangeIso_shift_hom]
      rfl)

instance changeFunctor_isTriangulated : (changeFunctor e).IsTriangulated where
  map_distinguished Δ hΔ := by
    obtain ⟨n, h₁, h₂, h₃, h⟩ := hΔ
    exact ⟨n, h₁, h₂, h₃, (distinguished_iff_of_iso
      (changeFunctorStageTriangleIso e Δ n h₁ h₂ h₃)).1 h⟩

end CategoryTheory.Stabilization
