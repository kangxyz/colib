/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.ShiftStages
public import Colib.CategoryTheory.Triangulated.Stabilization.FiniteDiagrams
public import Colib.CategoryTheory.Triangulated.Stabilization.Additive

/-! # Cohomological shift on finite-twist stabilization -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) [T.Full] [T.Faithful]
  [HasShift C ℤ] [T.CommShift ℤ]

/-- Shift a stable morphism using the shift commutation of the iterates of `T`. -/
def shiftMap (r : ℤ) {X Y : Stabilization T} (f : X ⟶ Y) :
    shiftObj T r X ⟶ shiftObj T r Y := by
  let n := max X.level Y.level
  change stage T (shiftObj T r X) n ⟶ stage T (shiftObj T r Y) n
  exact (stageShiftIso T r X n).hom ≫
    (shiftFunctor C r).map (show stage T X n ⟶ stage T Y n from f) ≫
      (stageShiftIso T r Y n).inv

set_option backward.isDefEq.respectTransparency false in
lemma homEquiv_shiftMap (r : ℤ) {X Y : Stabilization T} (f : X ⟶ Y)
    (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    homEquiv T (shiftObj T r X) (shiftObj T r Y) n hX hY (shiftMap T r f) =
      (stageShiftIso T r X n).hom ≫ (homEquiv T X Y n hX hY f)⟦r⟧' ≫
        (stageShiftIso T r Y n).inv :=
  transition_shift T r (Nat.le_max_left X.level Y.level) (Nat.le_max_right X.level Y.level)
    (max_le hX hY) f

set_option backward.isDefEq.respectTransparency false in
/-- The cohomological shift functor on the stabilization. -/
def shift (r : ℤ) : Stabilization T ⥤ Stabilization T where
  obj := shiftObj T r
  map f := shiftMap T r f
  map_id X := by
    have h : X.level ≤ X.level := le_rfl
    apply hom_ext T (X := shiftObj T r X) (Y := shiftObj T r X) X.level h h
    rw [homEquiv_shiftMap T r _ X.level h h]
    simp
  map_comp {X Y Z} f g := by
    let n := max (max X.level Y.level) Z.level
    have hX : X.level ≤ n := by dsimp [n]; omega
    have hY : Y.level ≤ n := by dsimp [n]; omega
    have hZ : Z.level ≤ n := by dsimp [n]; omega
    apply hom_ext T (X := shiftObj T r X) (Y := shiftObj T r Z) n hX hZ
    rw [homEquiv_comp T (shiftMap T r f) (shiftMap T r g) n hX hY hZ,
      homEquiv_shiftMap T r (f ≫ g) n hX hZ, homEquiv_comp T f g n hX hY hZ,
      homEquiv_shiftMap T r f n hX hY, homEquiv_shiftMap T r g n hY hZ, Functor.map_comp]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma shift_map_atLevel (r : ℤ) (n : ℕ) {A B : C} (f : A ⟶ B) :
    (shift T r).map ((atLevel T n).map f) = (atLevel T n).map (f⟦r⟧') := by
  have hn : n ≤ n := le_rfl
  apply hom_ext T (X := (atLevel T n).obj (A⟦r⟧)) (Y := (atLevel T n).obj (B⟦r⟧)) n hn hn
  change homEquiv T _ _ n hn hn (shiftMap T r ((atLevel T n).map f)) = _
  rw [homEquiv_shiftMap T r ((atLevel T n).map f) n hn hn,
    homEquiv_atLevel_map_of_le T n n hn f, homEquiv_atLevel_map_of_le T n n hn (f⟦r⟧')]
  let F := iterate T (n - n)
  change (F.commShiftIso r).hom.app A ≫ (F.map f)⟦r⟧' ≫ (F.commShiftIso r).inv.app B = F.map (f⟦r⟧')
  rw [← F.commShiftIso_hom_naturality_assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- The zero-shift comparison, included at each object's own denominator. -/
def shiftZeroIso : shift T 0 ≅ 𝟭 (Stabilization T) :=
  NatIso.ofComponents (fun X => (atLevel T X.level).mapIso ((shiftFunctorZero C ℤ).app X.obj)) (by
    intro X Y f
    let n := max X.level Y.level
    have hX : X.level ≤ n := Nat.le_max_left _ _
    have hY : Y.level ≤ n := Nat.le_max_right _ _
    let z (A : Stabilization T) : shiftObj T 0 A ⟶ A :=
      (atLevel T A.level).map ((shiftFunctorZero C ℤ).hom.app A.obj)
    have hz (A : Stabilization T) (hA : A.level ≤ n) :
        homEquiv T (shiftObj T 0 A) A n hA hA (z A) =
          (iterate T (n - A.level)).map ((shiftFunctorZero C ℤ).hom.app A.obj) :=
      homEquiv_atLevel_map_of_le T A.level n hA _
    change shiftMap T 0 f ≫ z Y = z X ≫ f
    apply hom_ext T (X := shiftObj T 0 X) (Y := Y) n hX hY
    rw [homEquiv_comp T (shiftMap T 0 f) (z Y) n hX hY hY,
      homEquiv_comp T (z X) f n hX hX hY, homEquiv_shiftMap T 0 f n hX hY,
      hz Y hY, hz X hX]
    let F := iterate T (n - X.level)
    let G := iterate T (n - Y.level)
    let g : F.obj X.obj ⟶ G.obj Y.obj := homEquiv T X Y n hX hY f
    simp only [Category.assoc]
    change (F.commShiftIso 0).hom.app X.obj ≫ g⟦(0 : ℤ)⟧' ≫
      (G.commShiftIso 0).inv.app Y.obj ≫ G.map ((shiftFunctorZero C ℤ).hom.app Y.obj) =
      F.map ((shiftFunctorZero C ℤ).hom.app X.obj) ≫ g
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      Functor.CommShift.isoZero_inv_app, Category.assoc, ← G.map_comp, Iso.inv_hom_id_app]
    erw [G.map_id ((𝟭 C).obj Y.obj), Category.comp_id]
    have e := (shiftFunctorZero C ℤ).hom.naturality g
    change g⟦(0 : ℤ)⟧' ≫ (shiftFunctorZero C ℤ).hom.app (G.obj Y.obj) =
      (shiftFunctorZero C ℤ).hom.app (F.obj X.obj) ≫ g at e
    erw [e, Iso.inv_hom_id_app_assoc])

set_option backward.isDefEq.respectTransparency false in
/-- The shift-addition comparison, included at each object's own denominator. -/
def shiftAddIso (r s : ℤ) : shift T (r + s) ≅ shift T r ⋙ shift T s :=
  NatIso.ofComponents (fun X => (atLevel T X.level).mapIso ((shiftFunctorAdd C r s).app X.obj)) (by
    intro X Y f
    let n := max X.level Y.level
    have hX : X.level ≤ n := Nat.le_max_left _ _
    have hY : Y.level ≤ n := Nat.le_max_right _ _
    let a (A : Stabilization T) : shiftObj T (r + s) A ⟶ shiftObj T s (shiftObj T r A) :=
      (atLevel T A.level).map ((shiftFunctorAdd C r s).hom.app A.obj)
    have ha (A : Stabilization T) (hA : A.level ≤ n) :
        homEquiv T (shiftObj T (r + s) A) (shiftObj T s (shiftObj T r A)) n hA hA (a A) =
          (iterate T (n - A.level)).map ((shiftFunctorAdd C r s).hom.app A.obj) :=
      homEquiv_atLevel_map_of_le T A.level n hA _
    change shiftMap T (r + s) f ≫ a Y = a X ≫ shiftMap T s (shiftMap T r f)
    apply hom_ext T (X := shiftObj T (r + s) X) (Y := shiftObj T s (shiftObj T r Y)) n hX hY
    rw [homEquiv_comp T (shiftMap T (r + s) f) (a Y) n hX hY hY,
      homEquiv_comp T (a X) (shiftMap T s (shiftMap T r f)) n hX hX hY,
      homEquiv_shiftMap T (r + s) f n hX hY, ha Y hY, ha X hX,
      homEquiv_shiftMap T s (shiftMap T r f) n hX hY, homEquiv_shiftMap T r f n hX hY]
    let F := iterate T (n - X.level)
    let G := iterate T (n - Y.level)
    let g : F.obj X.obj ⟶ G.obj Y.obj := homEquiv T X Y n hX hY f
    simp only [Category.assoc]
    change (F.commShiftIso (r + s)).hom.app X.obj ≫ g⟦r + s⟧' ≫
      (G.commShiftIso (r + s)).inv.app Y.obj ≫ G.map ((shiftFunctorAdd C r s).hom.app Y.obj) =
      F.map ((shiftFunctorAdd C r s).hom.app X.obj) ≫
        (F.commShiftIso s).hom.app (X.obj⟦r⟧) ≫
          ((F.commShiftIso r).hom.app X.obj ≫ g⟦r⟧' ≫ (G.commShiftIso r).inv.app Y.obj)⟦s⟧' ≫
            (G.commShiftIso s).inv.app (Y.obj⟦r⟧)
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      Functor.CommShift.isoAdd_inv_app, (shiftFunctor C s).map_comp, Category.assoc,
      ← G.map_comp, Iso.inv_hom_id_app]
    erw [G.map_id ((shiftFunctor C r ⋙ shiftFunctor C s).obj Y.obj), Category.comp_id]
    have e := (shiftFunctorAdd C r s).hom.naturality g
    change g⟦r + s⟧' ≫ (shiftFunctorAdd C r s).hom.app (G.obj Y.obj) =
      (shiftFunctorAdd C r s).hom.app (F.obj X.obj) ≫ (g⟦r⟧')⟦s⟧' at e
    simp only [reassoc_of% e, Iso.inv_hom_id_app_assoc])

set_option backward.isDefEq.respectTransparency false in
/-- The coherent shift data descended from the original category. -/
def shiftCore : ShiftMkCore (Stabilization T) ℤ where
  F := shift T
  zero := shiftZeroIso T
  add := shiftAddIso T
  assoc_hom_app r s t X := by
    let e : X.obj⟦(r + s) + t⟧ = X.obj⟦r + (s + t)⟧ := by rw [add_assoc]
    have h := congrArg ((atLevel T X.level).map)
      (shiftFunctorAdd_assoc_hom_app (C := C) r s t X.obj)
    change (atLevel T X.level).map ((shiftFunctorAdd C (r + s) t).hom.app X.obj) ≫
      (shift T t).map ((atLevel T X.level).map ((shiftFunctorAdd C r s).hom.app X.obj)) =
      eqToHom (congrArg (atLevel T X.level).obj e) ≫
        (atLevel T X.level).map ((shiftFunctorAdd C r (s + t)).hom.app X.obj) ≫
          (atLevel T X.level).map ((shiftFunctorAdd C s t).hom.app (X.obj⟦r⟧))
    rw [shift_map_atLevel, ← eqToHom_map (atLevel T X.level) e, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp]
    simpa only [shiftFunctorAdd', Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
      eqToHom_app, Category.assoc] using h
  zero_add_hom_app r X := by
    let e : X.obj⟦0 + r⟧ = X.obj⟦r⟧ := by rw [zero_add]
    change (atLevel T X.level).map ((shiftFunctorAdd C 0 r).hom.app X.obj) =
      eqToHom (congrArg (atLevel T X.level).obj e) ≫
        (shift T r).map ((atLevel T X.level).map ((shiftFunctorZero C ℤ).inv.app X.obj))
    rw [shift_map_atLevel, ← eqToHom_map (atLevel T X.level) e, ← Functor.map_comp]
    exact congrArg ((atLevel T X.level).map) (shiftFunctorAdd_zero_add_hom_app (C := C) r X.obj)
  add_zero_hom_app r X := by
    let e : X.obj⟦r + 0⟧ = X.obj⟦r⟧ := by rw [add_zero]
    change (atLevel T X.level).map ((shiftFunctorAdd C r 0).hom.app X.obj) =
      eqToHom (congrArg (atLevel T X.level).obj e) ≫
        (atLevel T X.level).map ((shiftFunctorZero C ℤ).inv.app (X.obj⟦r⟧))
    rw [← eqToHom_map (atLevel T X.level) e, ← Functor.map_comp]
    exact congrArg ((atLevel T X.level).map) (shiftFunctorAdd_add_zero_hom_app (C := C) r X.obj)

instance : HasShift (Stabilization T) ℤ := hasShiftMk _ _ (shiftCore T)

@[simp] lemma shift_obj_level (r : ℤ) (X : Stabilization T) : (X⟦r⟧).level = X.level := rfl

@[simp] lemma shift_obj_obj (r : ℤ) (X : Stabilization T) : (X⟦r⟧).obj = X.obj⟦r⟧ := rfl

lemma homEquiv_shift (r : ℤ) {X Y : Stabilization T} (f : X ⟶ Y)
    (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    homEquiv T (X⟦r⟧) (Y⟦r⟧) n hX hY (f⟦r⟧') =
      (stageShiftIso T r X n).hom ≫ (homEquiv T X Y n hX hY f)⟦r⟧' ≫
        (stageShiftIso T r Y n).inv := homEquiv_shiftMap T r f n hX hY

/-- Inclusion at every denominator commutes with cohomological shift. -/
def atLevelCommShiftIso (n : ℕ) (r : ℤ) :
    shiftFunctor C r ⋙ atLevel T n ≅ atLevel T n ⋙ shiftFunctor (Stabilization T) r :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    change (atLevel T n).map (f⟦r⟧') ≫ 𝟙 _ =
      𝟙 _ ≫ (shift T r).map ((atLevel T n).map f)
    rw [Category.comp_id, Category.id_comp, shift_map_atLevel])

set_option backward.isDefEq.respectTransparency false in
instance atLevelCommShift (n : ℕ) : (atLevel T n).CommShift ℤ where
  commShiftIso := atLevelCommShiftIso T n
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app]
    change 𝟙 ((atLevel T n).obj (X⟦(0 : ℤ)⟧)) =
      (atLevel T n).map ((shiftFunctorZero C ℤ).hom.app X) ≫
        (atLevel T n).map ((shiftFunctorZero C ℤ).inv.app X)
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  commShiftIso_add r s := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app]
    change 𝟙 ((atLevel T n).obj (X⟦r + s⟧)) =
      (atLevel T n).map ((shiftFunctorAdd C r s).hom.app X) ≫
        𝟙 ((atLevel T n).obj ((X⟦r⟧)⟦s⟧)) ≫
          (shift T s).map (𝟙 ((atLevel T n).obj (X⟦r⟧))) ≫
            (atLevel T n).map ((shiftFunctorAdd C r s).inv.app X)
    have e : (shift T s).map (𝟙 ((atLevel T n).obj (X⟦r⟧))) =
        𝟙 ((atLevel T n).obj ((X⟦r⟧)⟦s⟧)) := (shift T s).map_id _
    erw [e, Category.id_comp, Category.id_comp, ← Functor.map_comp,
      Iso.hom_inv_id_app, Functor.map_id]

instance [Preadditive C] [T.Additive] [∀ r : ℤ, (shiftFunctor C r).Additive]
    (r : ℤ) : (shiftFunctor (Stabilization T) r).Additive where
  map_add {X Y f g} := by
    let n := max X.level Y.level
    let A := stage T X n
    let B := stage T Y n
    let eX := stageShiftIso T r X n
    let eY := stageShiftIso T r Y n
    let fₙ : A ⟶ B := f
    let gₙ : A ⟶ B := g
    change eX.hom ≫ (fₙ + gₙ)⟦r⟧' ≫ eY.inv =
      (eX.hom ≫ fₙ⟦r⟧' ≫ eY.inv) + (eX.hom ≫ gₙ⟦r⟧' ≫ eY.inv)
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

end CategoryTheory.Stabilization
