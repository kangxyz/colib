/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Inverse
public import Colib.CategoryTheory.Triangulated.Stabilization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Exact inversion of the stabilizing endofunctor -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open Pretriangulated Limits CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) [T.Full] [T.Faithful]

set_option backward.isDefEq.respectTransparency false in
lemma inverseTwist_map_atLevel (n : ℕ) {A B : C} (f : A ⟶ B) :
    (inverseTwist T).map ((atLevel T n).map f) = (atLevel T (n + 1)).map f := by
  have hn : n ≤ n := le_rfl
  have hn' : n + 1 ≤ n + 1 := le_rfl
  apply hom_ext T (X := (atLevel T (n + 1)).obj A) (Y := (atLevel T (n + 1)).obj B) (n + 1) hn' hn'
  change homEquiv T _ _ (n + 1) hn' hn' (inverseTwistHomEquiv T _ _ ((atLevel T n).map f)) = _
  rw [homEquiv_inverseTwistHomEquiv T ((atLevel T n).map f) n hn hn,
    homEquiv_atLevel_map_of_le T n n hn f, homEquiv_atLevel_map_of_le T (n + 1) (n + 1) hn' f]
  have e : n + 1 - (n + 1) = n - n := by omega
  exact (Functor.congr_hom (congrArg (iterate T) e) f).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original endofunctor becomes inverse to denominator increment on the included category. -/
def inverseTwistInclusionIso : T ⋙ inclusion T ⋙ inverseTwist T ≅ inclusion T :=
  NatIso.ofComponents (fun A => inverseTwistObjIso T ((inclusion T).obj A)) (by
    intro A B f
    let z (D : C) : (atLevel T 1).obj (T.obj D) ⟶ (inclusion T).obj D :=
      (inverseTwistObjIso T ((inclusion T).obj D)).hom
    have h₁ : 1 ≤ 1 := le_rfl
    have h₀ : 0 ≤ 1 := Nat.zero_le 1
    have hz (D : C) :
        homEquiv T ((atLevel T 1).obj (T.obj D)) ((inclusion T).obj D) 1 h₁ h₀ (z D) =
          𝟙 (T.obj D) := by
      let e := homEquiv T ((atLevel T 1).obj (T.obj D)) ((inclusion T).obj D) 1 h₁ h₀
      change e (e.symm (𝟙 (T.obj D))) = _
      exact e.apply_symm_apply _
    change (inverseTwist T).map ((atLevel T 0).map (T.map f)) ≫ z B =
      z A ≫ (atLevel T 0).map f
    rw [inverseTwist_map_atLevel T 0]
    apply hom_ext T (X := (atLevel T 1).obj (T.obj A)) (Y := (inclusion T).obj B) 1 h₁ h₀
    rw [homEquiv_comp T ((atLevel T 1).map (T.map f)) (z B) 1 h₁ h₁ h₀,
      homEquiv_comp T (z A) ((atLevel T 0).map f) 1 h₁ h₀ h₀, hz A, hz B,
      homEquiv_atLevel_map_of_le T 1 1 h₁ (T.map f), homEquiv_atLevel_map_of_le T 0 1 h₀ f]
    change T.map f ≫ 𝟙 _ = 𝟙 _ ≫ T.map f
    rw [Category.comp_id, Category.id_comp])

/-- The positive stable twist extends the original endofunctor, up to its canonical isomorphism. -/
def twistInclusionIso : inclusion T ⋙ (twistEquivalence T).functor ≅ T ⋙ inclusion T :=
  (isoWhiskerLeft (T ⋙ inclusion T) (inverseTwistEquivalence T).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((Functor.associator T (inclusion T) (inverseTwist T)) ≪≫
      inverseTwistInclusionIso T) (inverseTwistEquivalence T).inverse).symm

variable [HasShift C ℤ] [T.CommShift ℤ]

omit [T.Full] [T.Faithful] in
private lemma inverseTwistStageIso_shift (r : ℤ) (X : Stabilization T) (n : ℕ) :
    inverseTwistStageIso T (shiftObj T r X) n ≪≫ stageShiftIso T r X n =
      stageShiftIso T r (inverseTwistObj T X) (n + 1) ≪≫
        (shiftFunctor C r).mapIso (inverseTwistStageIso T X n) := by
  have e (i j : ℕ) (h : i = j) (A : C) :
      eqToHom (congrArg (fun k => (iterate T k).obj (A⟦r⟧)) h) ≫
        ((iterate T j).commShiftIso r).hom.app A =
      ((iterate T i).commShiftIso r).hom.app A ≫
        (eqToHom (congrArg (fun k => (iterate T k).obj A) h))⟦r⟧' := by
    subst j
    simp
  apply Iso.ext
  exact e (n + 1 - (X.level + 1)) (n - X.level) (by omega) X.obj

set_option backward.isDefEq.respectTransparency false in
lemma inverseTwist_shift_map (r : ℤ) {X Y : Stabilization T} (f : X ⟶ Y) :
    (inverseTwist T).map (f⟦r⟧') = ((inverseTwist T).map f)⟦r⟧' := by
  let n := max X.level Y.level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have hY : Y.level ≤ n := Nat.le_max_right _ _
  have hX' : X.level + 1 ≤ n + 1 := Nat.add_le_add_right hX 1
  have hY' : Y.level + 1 ≤ n + 1 := Nat.add_le_add_right hY 1
  apply hom_ext T (X := inverseTwistObj T (shiftObj T r X))
    (Y := inverseTwistObj T (shiftObj T r Y)) (n + 1) hX' hY'
  change homEquiv T _ _ (n + 1) hX' hY' (inverseTwistHomEquiv T _ _ (f⟦r⟧')) =
    homEquiv T (shiftObj T r (inverseTwistObj T X)) (shiftObj T r (inverseTwistObj T Y))
      (n + 1) hX' hY' (((inverseTwist T).map f)⟦r⟧')
  erw [homEquiv_inverseTwistHomEquiv T (f⟦r⟧') n hX hY,
    homEquiv_shift T r f n hX hY,
    homEquiv_shift T r ((inverseTwist T).map f) (n + 1) hX' hY']
  change _ = _ ≫ (homEquiv T _ _ (n + 1) hX' hY' (inverseTwistHomEquiv T _ _ f))⟦r⟧' ≫ _
  erw [homEquiv_inverseTwistHomEquiv T f n hX hY]
  have eX := congrArg Iso.hom (inverseTwistStageIso_shift T r X n)
  have eY := congrArg Iso.inv (inverseTwistStageIso_shift T r Y n)
  simp only [Iso.trans_hom, Functor.mapIso_hom] at eX
  simp only [Iso.trans_inv, Functor.mapIso_inv] at eY
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% eX, eY]
  rfl

/-- Denominator increment commutes with the cohomological shift. -/
def inverseTwistCommShiftIso (r : ℤ) :
    shiftFunctor (Stabilization T) r ⋙ inverseTwist T ≅
      inverseTwist T ⋙ shiftFunctor (Stabilization T) r :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change (inverseTwist T).map (f⟦r⟧') ≫ 𝟙 _ = 𝟙 _ ≫ ((inverseTwist T).map f)⟦r⟧'
    rw [Category.comp_id, Category.id_comp, inverseTwist_shift_map])

set_option backward.isDefEq.respectTransparency false in
instance inverseTwistCommShift : (inverseTwist T).CommShift ℤ where
  commShiftIso := inverseTwistCommShiftIso T
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app]
    change 𝟙 ((atLevel T (X.level + 1)).obj (X.obj⟦(0 : ℤ)⟧)) =
      (inverseTwist T).map ((atLevel T X.level).map ((shiftFunctorZero C ℤ).hom.app X.obj)) ≫
        (atLevel T (X.level + 1)).map ((shiftFunctorZero C ℤ).inv.app X.obj)
    rw [inverseTwist_map_atLevel, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  commShiftIso_add r s := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app]
    let n := X.level + 1
    change 𝟙 ((atLevel T n).obj (X.obj⟦r + s⟧)) =
      (inverseTwist T).map ((atLevel T X.level).map ((shiftFunctorAdd C r s).hom.app X.obj)) ≫
        𝟙 ((atLevel T n).obj ((X.obj⟦r⟧)⟦s⟧)) ≫
          (shift T s).map (𝟙 ((atLevel T n).obj (X.obj⟦r⟧))) ≫
            (atLevel T n).map ((shiftFunctorAdd C r s).inv.app X.obj)
    have e : (shift T s).map (𝟙 ((atLevel T n).obj (X.obj⟦r⟧))) =
        𝟙 ((atLevel T n).obj ((X.obj⟦r⟧)⟦s⟧)) := (shift T s).map_id _
    erw [inverseTwist_map_atLevel, e, Category.id_comp, Category.id_comp, ← Functor.map_comp,
      Iso.hom_inv_id_app, Functor.map_id]

instance inverseTwistEquivalenceFunctorCommShift :
    (inverseTwistEquivalence T).functor.CommShift ℤ :=
  inferInstanceAs ((inverseTwist T).CommShift ℤ)

instance twistCommShift : (twistEquivalence T).functor.CommShift ℤ :=
  (inverseTwistEquivalence T).commShiftInverse ℤ

instance inverseTwistEquivalenceInverseCommShift :
    (inverseTwistEquivalence T).inverse.CommShift ℤ :=
  inferInstanceAs ((twistEquivalence T).functor.CommShift ℤ)

instance inverseTwistEquivalence_commShift : (inverseTwistEquivalence T).CommShift ℤ :=
  (inverseTwistEquivalence T).commShift_of_functor ℤ

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [T.IsTriangulated]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse twist has the same triangle at the next common stage. -/
def inverseTwistStageTriangleIso (Δ : Triangle (Stabilization T)) (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n) :
    stageTriangle T ((inverseTwist T).mapTriangle.obj Δ) (n + 1)
      (Nat.add_le_add_right h₁ 1) (Nat.add_le_add_right h₂ 1) (Nat.add_le_add_right h₃ 1) ≅
      stageTriangle T Δ n h₁ h₂ h₃ :=
  Triangle.isoMk _ _ (inverseTwistStageIso T Δ.obj₁ n) (inverseTwistStageIso T Δ.obj₂ n)
    (inverseTwistStageIso T Δ.obj₃ n)
    (by
      change homEquiv T _ _ (n + 1) _ _ (inverseTwistHomEquiv T _ _ Δ.mor₁) ≫ _ = _
      rw [homEquiv_inverseTwistHomEquiv T _ n h₁ h₂]
      simp [stageTriangle])
    (by
      change homEquiv T _ _ (n + 1) _ _ (inverseTwistHomEquiv T _ _ Δ.mor₂) ≫ _ = _
      rw [homEquiv_inverseTwistHomEquiv T _ n h₂ h₃]
      simp [stageTriangle])
    (by
      change (homEquiv T (inverseTwistObj T Δ.obj₃) (inverseTwistObj T (Δ.obj₁⟦(1 : ℤ)⟧))
        (n + 1) (Nat.add_le_add_right h₃ 1) (Nat.add_le_add_right h₁ 1)
        (inverseTwistHomEquiv T _ _ Δ.mor₃ ≫ 𝟙 _) ≫
          (stageShiftIso T 1 (inverseTwistObj T Δ.obj₁) (n + 1)).hom) ≫
          ((inverseTwistStageIso T Δ.obj₁ n).hom)⟦(1 : ℤ)⟧' =
        (inverseTwistStageIso T Δ.obj₃ n).hom ≫
          homEquiv T Δ.obj₃ (Δ.obj₁⟦(1 : ℤ)⟧) n h₃ h₁ Δ.mor₃ ≫
            (stageShiftIso T 1 Δ.obj₁ n).hom
      erw [Category.comp_id, homEquiv_inverseTwistHomEquiv T Δ.mor₃ n h₃ h₁]
      have e := congrArg Iso.hom (inverseTwistStageIso_shift T 1 Δ.obj₁ n)
      simp only [Iso.trans_hom, Functor.mapIso_hom] at e
      simp only [Category.assoc]
      erw [← e, Iso.inv_hom_id_assoc])

instance inverseTwist_isTriangulated : (inverseTwist T).IsTriangulated where
  map_distinguished Δ hΔ := by
    obtain ⟨n, h₁, h₂, h₃, h⟩ := hΔ
    apply (distinguished_iff T _ (n + 1) (Nat.add_le_add_right h₁ 1)
      (Nat.add_le_add_right h₂ 1) (Nat.add_le_add_right h₃ 1)).2
    exact (distinguished_iff_of_iso (inverseTwistStageTriangleIso T Δ n h₁ h₂ h₃)).2 h

instance inverseTwistEquivalence_isTriangulated : (inverseTwistEquivalence T).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (inferInstanceAs ((inverseTwist T).IsTriangulated))

end CategoryTheory.Stabilization
