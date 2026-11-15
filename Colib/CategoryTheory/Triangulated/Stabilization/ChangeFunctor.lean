/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Additive
public import Colib.CategoryTheory.Triangulated.Stabilization.FiniteDiagrams
public import Colib.CategoryTheory.Triangulated.Stabilization.ShiftStages
public import Mathlib.CategoryTheory.Equivalence

/-! # Changing the endofunctor by a natural isomorphism -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] {T U : C ⥤ C} (e : T ≅ U)

/-- A natural isomorphism of transition functors acts on every finite iterate. -/
def iterateChangeIso : (n : ℕ) → iterate T n ≅ iterate U n
  | 0 => Iso.refl _
  | n + 1 => Functor.isoWhiskerRight (iterateChangeIso n) T ≪≫
      Functor.isoWhiskerLeft (iterate U n) e

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem iterateChangeIso_add_hom (a b : ℕ) (X : C) :
    (iterateAddIso T a b).hom.app X ≫
        (iterate T b).map ((iterateChangeIso e a).hom.app X) ≫
        (iterateChangeIso e b).hom.app ((iterate U a).obj X) =
      (iterateChangeIso e (a + b)).hom.app X ≫ (iterateAddIso U a b).hom.app X := by
  induction b with
  | zero => simp [iterateChangeIso, iterateAddIso]
  | succ b ih =>
    simp only [Nat.add_succ, iterateChangeIso, iterateAddIso, iterate_succ,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id, Functor.comp_map,
      Category.assoc, ← T.map_comp_assoc, ih]
    rw [T.map_comp, Category.assoc, e.hom.naturality]
    rfl

/-- An object keeps its numerator and denominator when the transition is changed. -/
abbrev changeObj (X : Stabilization T) : Stabilization U := ⟨X.obj, X.level⟩

/-- The two realizations of a numerator at the same stage are canonically isomorphic. -/
def stageChangeIso (X : Stabilization T) (n : ℕ) :
    stage T X n ≅ stage U (changeObj (U := U) X) n :=
  (iterateChangeIso e (n - X.level)).app X.obj

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem stageChangeIso_transition_hom (X : Stabilization T) {m n : ℕ}
    (hX : X.level ≤ m) (h : m ≤ n) :
    (stageIso T X hX h).hom ≫ (stageChangeIso e X n).hom =
      (iterate T (n - m)).map (stageChangeIso e X m).hom ≫
        (iterateChangeIso e (n - m)).hom.app (stage U (changeObj (U := U) X) m) ≫
        (stageIso U (changeObj (U := U) X) hX h).hom := by
  let a := m - X.level
  let b := n - m
  have hsum : a + b = n - X.level := by dsimp [a, b]; omega
  have hn := eqToHom_iso_hom_naturality
    (fun j : ℕ => (iterateChangeIso e j).app X.obj) hsum
  have ht := iterateChangeIso_add_hom e a b X.obj
  have ht' := congrArg (fun f => (iterateAddIso T a b).inv.app X.obj ≫ f ≫
    (iterateAddIso U a b).inv.app X.obj) ht
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc] at ht'
  rw [Iso.hom_inv_id_app, Category.comp_id] at ht'
  have hT := congrArg Iso.hom (stageFunctorIso_app T X hX h)
  have hU := congrArg Iso.hom (stageFunctorIso_app U (changeObj (U := U) X) hX h)
  simp only [Iso.app_hom, stageFunctorIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    eqToIso.hom, eqToHom_app] at hT hU
  rw [← hT, ← hU, Category.assoc]
  change (iterateAddIso T a b).inv.app X.obj ≫
      eqToHom (congrArg (fun j => (iterate T j).obj X.obj) hsum) ≫
      ((iterateChangeIso e (n - X.level)).app X.obj).hom =
    (iterate T b).map ((iterateChangeIso e a).hom.app X.obj) ≫
      (iterateChangeIso e b).hom.app ((iterate U a).obj X.obj) ≫
      ((iterateAddIso U a b).inv.app X.obj ≫
        eqToHom (congrArg (fun j => (iterate U j).obj X.obj) hsum))
  rw [← hn]
  simpa only [Category.assoc, Iso.app_hom] using
    congrArg (· ≫ eqToHom (congrArg (fun j => (iterate U j).obj X.obj) hsum)) ht'.symm

set_option backward.isDefEq.respectTransparency false in
/-- The finite transition maps commute with change of the original endofunctor. -/
theorem transition_change {X Y : Stabilization T} {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n)
    (f : stage T X m ⟶ stage T Y m) :
    transition U (X := changeObj X) (Y := changeObj Y) hX hY h
        ((stageChangeIso e X m).homCongr (stageChangeIso e Y m) f) =
      (stageChangeIso e X n).homCongr (stageChangeIso e Y n) (transition T hX hY h f) := by
  apply (cancel_epi ((stageIso T X hX h).hom ≫ (stageChangeIso e X n).hom)).mp
  simp only [transition, Iso.homCongr_apply, Category.assoc, Functor.map_comp,
    Iso.hom_inv_id_assoc]
  rw [stageChangeIso_transition_hom_assoc, stageChangeIso_transition_hom]
  simp only [Iso.hom_inv_id_assoc]
  let b := n - m
  let g := ((stageChangeIso e X m).inv ≫ f) ≫ (stageChangeIso e Y m).hom
  rw [← (iterate U b).map_comp_assoc, ← (iterate U b).map_comp_assoc]
  have hnat := (iterateChangeIso e b).hom.naturality g
  change (iterate T b).map g ≫ (iterateChangeIso e b).hom.app (stage U (changeObj Y) m) =
    (iterateChangeIso e b).hom.app (stage U (changeObj X) m) ≫ (iterate U b).map g at hnat
  rw [← reassoc_of% hnat, ← (iterate T b).map_comp_assoc]
  dsimp only [g]
  simp [b]

variable [T.Full] [T.Faithful] [U.Full] [U.Faithful]

/-- Changing the endofunctor acts by the canonical isomorphisms on stage Hom sets. -/
def changeHomEquiv (X Y : Stabilization T) :
    (X ⟶ Y) ≃ ((changeObj (U := U) X) ⟶ changeObj Y) :=
  (stageChangeIso e X (max X.level Y.level)).homCongr
    (stageChangeIso e Y (max X.level Y.level))

/-- The equivalence on Hom sets is compatible with realization at a common stage. -/
theorem homEquiv_changeHomEquiv {X Y : Stabilization T} (f : X ⟶ Y)
    (n : ℕ) (hX : X.level ≤ n) (hY : Y.level ≤ n) :
    homEquiv U (changeObj X) (changeObj Y) n hX hY (changeHomEquiv e X Y f) =
      (stageChangeIso e X n).homCongr (stageChangeIso e Y n)
        (homEquiv T X Y n hX hY f) :=
  transition_change e (Nat.le_max_left _ _) (Nat.le_max_right _ _) (max_le hX hY) f

/-- Change the transition by the original natural isomorphism. -/
def changeFunctor : Stabilization T ⥤ Stabilization U where
  obj := changeObj
  map {X Y} f := changeHomEquiv e X Y f
  map_id X := by
    change (stageChangeIso e X _).inv ≫ 𝟙 _ ≫ (stageChangeIso e X _).hom = 𝟙 _
    simp
  map_comp {X Y Z} f g := by
    let n := max (max X.level Y.level) Z.level
    have hX : X.level ≤ n := by dsimp [n]; omega
    have hY : Y.level ≤ n := by dsimp [n]; omega
    have hZ : Z.level ≤ n := by dsimp [n]; omega
    apply hom_ext U (X := changeObj X) (Y := changeObj Z) n hX hZ
    rw [homEquiv_comp U (X := changeObj X) (Y := changeObj Y) (Z := changeObj Z)
      _ _ n hX hY hZ]
    rw [homEquiv_changeHomEquiv, homEquiv_changeHomEquiv, homEquiv_changeHomEquiv,
      homEquiv_comp T f g n hX hY hZ, Iso.homCongr_comp]

/-- Changing the transition preserves the original maps at each fixed denominator. -/
theorem changeFunctor_map_atLevel (n : ℕ) {A B : C} (f : A ⟶ B) :
    (changeFunctor e).map ((atLevel T n).map f) = (atLevel U n).map f := by
  let X : Stabilization T := (atLevel T n).obj A
  let Y : Stabilization T := (atLevel T n).obj B
  have hX : X.level ≤ n := Nat.le_refl n
  have hY : Y.level ≤ n := Nat.le_refl n
  apply hom_ext U (X := changeObj X) (Y := changeObj Y) n hX hY
  change homEquiv U (changeObj X) (changeObj Y) n hX hY
      (changeHomEquiv e X Y ((atLevel T n).map f)) = _
  rw [homEquiv_changeHomEquiv e]
  erw [homEquiv_atLevel_map_of_le T n n (Nat.le_refl n) f,
    homEquiv_atLevel_map_of_le U n n (Nat.le_refl n) f]
  let a := (iterateChangeIso e (n - n)).app A
  let b := (iterateChangeIso e (n - n)).app B
  change a.inv ≫ (iterate T (n - n)).map f ≫ b.hom = (iterate U (n - n)).map f
  have he : (iterate T (n - n)).map f ≫ b.hom = a.hom ≫ (iterate U (n - n)).map f :=
    (iterateChangeIso e (n - n)).hom.naturality f
  rw [he, Iso.inv_hom_id_assoc]

/-- The change of transition identifies the two original denominator-zero inclusions. -/
def inclusionChangeFunctorIso : inclusion T ⋙ changeFunctor e ≅ inclusion U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change (changeFunctor e).map ((inclusion T).map f) ≫ 𝟙 _ = 𝟙 _ ≫ (inclusion U).map f
    rw [Category.comp_id, Category.id_comp, changeFunctor_map_atLevel])

instance : (changeFunctor e).Full where
  map_surjective {X Y} := (changeHomEquiv e X Y).surjective

instance : (changeFunctor e).Faithful where
  map_injective {X Y} := (changeHomEquiv e X Y).injective

instance : (changeFunctor e).EssSurj where
  mem_essImage X := by
    obtain ⟨A, n⟩ := X
    exact ⟨⟨A, n⟩, ⟨Iso.refl _⟩⟩

/-- Naturally isomorphic transitions have equivalent finite-stage categories. -/
def changeEquivalence : Stabilization T ≌ Stabilization U :=
  let : (changeFunctor e).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  (changeFunctor e).asEquivalence

set_option backward.isDefEq.respectTransparency false in
instance [Preadditive C] [T.Additive] [U.Additive] : (changeFunctor e).Additive where
  map_add {X Y} f g := by
    let n := max X.level Y.level
    let a := stageChangeIso e X n
    let b := stageChangeIso e Y n
    change a.inv ≫ (f + g) ≫ b.hom = (a.inv ≫ f ≫ b.hom) + (a.inv ≫ g ≫ b.hom)
    simp only [Preadditive.add_comp, Preadditive.comp_add]

end CategoryTheory.Stabilization
