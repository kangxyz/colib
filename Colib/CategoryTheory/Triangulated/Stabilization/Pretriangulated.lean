/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Triangles

/-! # The pretriangulated structure on finite-twist stabilization

The pretriangulated axioms are transported from a common finite stage. No
localization of the original category at a class of its morphisms is used.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open Pretriangulated Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (T : C ⥤ C) [T.Full] [T.Faithful] [T.CommShift ℤ] [T.IsTriangulated]

/-- Zero objects remain zero at every admissible finite stage. -/
lemma stage_isZero {X : Stabilization T} (hX : IsZero X) (n : ℕ) (hn : X.level ≤ n) :
    IsZero (stage T X n) := by
  rw [IsZero.iff_id_eq_zero, ← homEquiv_id T X n hn, (IsZero.iff_id_eq_zero X).1 hX,
    homEquiv_zero]

/-- The distinguished-triangle predicate is invariant under isomorphism. -/
lemma distinguished_of_iso {Δ Δ' : Triangle (Stabilization T)} (e : Δ ≅ Δ')
    (hΔ : Distinguished T Δ) : Distinguished T Δ' := by
  let n := Δ.obj₁.level + Δ.obj₂.level + Δ.obj₃.level +
    Δ'.obj₁.level + Δ'.obj₂.level + Δ'.obj₃.level
  have h₁ : Δ.obj₁.level ≤ n := by dsimp [n]; omega
  have h₂ : Δ.obj₂.level ≤ n := by dsimp [n]; omega
  have h₃ : Δ.obj₃.level ≤ n := by dsimp [n]; omega
  have h₁' : Δ'.obj₁.level ≤ n := by dsimp [n]; omega
  have h₂' : Δ'.obj₂.level ≤ n := by dsimp [n]; omega
  have h₃' : Δ'.obj₃.level ≤ n := by dsimp [n]; omega
  exact (distinguished_iff T Δ' n h₁' h₂' h₃').2
    ((distinguished_iff_of_iso (stageTriangleIso T e n h₁ h₂ h₃ h₁' h₂' h₃')).1
      ((distinguished_iff T Δ n h₁ h₂ h₃).1 hΔ))

/-- Contractible triangles are distinguished after formal inversion. -/
lemma contractible_distinguished (X : Stabilization T) :
    Distinguished T (contractibleTriangle X) := by
  let n := max X.level (0 : Stabilization T).level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have h0 : (0 : Stabilization T).level ≤ n := Nat.le_max_right _ _
  apply (distinguished_iff T (contractibleTriangle X) n hX hX h0).2
  let e := (stage_isZero T (isZero_zero (Stabilization T)) n h0).isoZero
  let i : stageTriangle T (contractibleTriangle X) n hX hX h0 ≅
      contractibleTriangle (stage T X n) :=
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
      (by
        change homEquiv T X X n hX hX (𝟙 X) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        rw [homEquiv_id, Category.comp_id])
      (by
        change homEquiv T X 0 n hX h0 0 ≫ e.hom = 𝟙 _ ≫ 0
        rw [homEquiv_zero, zero_comp, comp_zero])
      (by
        change (homEquiv T 0 (X⟦(1 : ℤ)⟧) n h0 hX 0 ≫ (stageShiftIso T 1 X n).hom) ≫
          (𝟙 (stage T X n))⟦(1 : ℤ)⟧' = e.hom ≫ 0
        erw [homEquiv_zero T (0 : Stabilization T) (X⟦(1 : ℤ)⟧) n h0 hX,
          zero_comp, zero_comp, comp_zero])
  exact (distinguished_iff_of_iso i).2 (Pretriangulated.contractible_distinguished _)

/-- Every stable morphism has a distinguished cone, constructed at one finite stage. -/
lemma distinguished_cocone_triangle {X Y : Stabilization T} (f : X ⟶ Y) :
    ∃ (Z : Stabilization T) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Distinguished T (Triangle.mk f g h) := by
  let n := max X.level Y.level
  have hX : X.level ≤ n := Nat.le_max_left _ _
  have hY : Y.level ≤ n := Nat.le_max_right _ _
  obtain ⟨Z, g, h, hΔ⟩ :=
    Pretriangulated.distinguished_cocone_triangle (homEquiv T X Y n hX hY f)
  let Z' := (atLevel T n).obj Z
  let e := atLevelStageIso T n Z
  have hZ : Z'.level ≤ n := le_rfl
  let g' : Y ⟶ Z' := (homEquiv T Y Z' n hY hZ).symm (g ≫ e.inv)
  let h' : Z' ⟶ X⟦(1 : ℤ)⟧ :=
    (homEquiv T Z' (X⟦(1 : ℤ)⟧) n hZ hX).symm
      (e.hom ≫ h ≫ (stageShiftIso T 1 X n).inv)
  refine ⟨Z', g', h', (distinguished_iff T _ n hX hY hZ).2 ?_⟩
  let i : stageTriangle T (Triangle.mk f g' h') n hX hY hZ ≅
      Triangle.mk (homEquiv T X Y n hX hY f) g h :=
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
      (by simp [stageTriangle]) (by simp [stageTriangle, g']) (by
        change (homEquiv T Z' (X⟦(1 : ℤ)⟧) n hZ hX h' ≫
          (stageShiftIso T 1 X n).hom) ≫ (𝟙 (stage T X n))⟦(1 : ℤ)⟧' = e.hom ≫ h
        dsimp only [h']
        erw [Equiv.apply_symm_apply, Functor.map_id, Category.comp_id,
          Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact (distinguished_iff_of_iso i).2 hΔ

set_option backward.isDefEq.respectTransparency false in
/-- Rotation of a stable triangle is rotation of its realization, up to the prescribed shift map. -/
def stageTriangleRotateIso (Δ : Triangle (Stabilization T)) (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n) :
    stageTriangle T Δ.rotate n h₂ h₃ h₁ ≅ (stageTriangle T Δ n h₁ h₂ h₃).rotate :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (stageShiftIso T 1 Δ.obj₁ n)
    (by
      change homEquiv T Δ.obj₂ Δ.obj₃ n h₂ h₃ Δ.mor₂ ≫ 𝟙 _ =
        𝟙 _ ≫ homEquiv T Δ.obj₂ Δ.obj₃ n h₂ h₃ Δ.mor₂
      rw [Category.comp_id, Category.id_comp])
    (by
      change homEquiv T Δ.obj₃ (Δ.obj₁⟦(1 : ℤ)⟧) n h₃ h₁ Δ.mor₃ ≫
        (stageShiftIso T 1 Δ.obj₁ n).hom = 𝟙 _ ≫
          homEquiv T Δ.obj₃ (Δ.obj₁⟦(1 : ℤ)⟧) n h₃ h₁ Δ.mor₃ ≫ (stageShiftIso T 1 Δ.obj₁ n).hom
      rw [Category.id_comp])
    (by
      change ((homEquiv T (Δ.obj₁⟦(1 : ℤ)⟧) (Δ.obj₂⟦(1 : ℤ)⟧) n h₁ h₂
        (-Δ.mor₁⟦(1 : ℤ)⟧')) ≫ (stageShiftIso T 1 Δ.obj₂ n).hom) ≫
          (𝟙 (stage T Δ.obj₂ n))⟦(1 : ℤ)⟧' =
        (stageShiftIso T 1 Δ.obj₁ n).hom ≫ (-((homEquiv T Δ.obj₁ Δ.obj₂ n h₁ h₂ Δ.mor₁)⟦(1 : ℤ)⟧'))
      rw [Functor.map_id, Category.comp_id, homEquiv_neg, homEquiv_shift T 1 Δ.mor₁ n h₁ h₂]
      rw [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc, Category.assoc]
      erw [Iso.inv_hom_id, Category.comp_id])

/-- The rotation axiom is inherited from the common finite stage. -/
lemma rotate_distinguished_triangle (Δ : Triangle (Stabilization T)) :
    Distinguished T Δ ↔ Distinguished T Δ.rotate := by
  let n := Δ.obj₁.level + Δ.obj₂.level + Δ.obj₃.level
  have h₁ : Δ.obj₁.level ≤ n := by dsimp [n]; omega
  have h₂ : Δ.obj₂.level ≤ n := by dsimp [n]; omega
  have h₃ : Δ.obj₃.level ≤ n := by dsimp [n]; omega
  rw [distinguished_iff T Δ n h₁ h₂ h₃,
    distinguished_iff T Δ.rotate n h₂ h₃ h₁,
    distinguished_iff_of_iso (stageTriangleRotateIso T Δ n h₁ h₂ h₃)]
  exact Pretriangulated.rotate_distinguished_triangle _

set_option backward.isDefEq.respectTransparency false in
/-- A commutative square between distinguished stable triangles completes at a finite stage. -/
lemma complete_distinguished_triangle_morphism (Δ Δ' : Triangle (Stabilization T))
    (hΔ : Distinguished T Δ) (hΔ' : Distinguished T Δ')
    (a : Δ.obj₁ ⟶ Δ'.obj₁) (b : Δ.obj₂ ⟶ Δ'.obj₂) (hab : Δ.mor₁ ≫ b = a ≫ Δ'.mor₁) :
    ∃ c : Δ.obj₃ ⟶ Δ'.obj₃, Δ.mor₂ ≫ c = b ≫ Δ'.mor₂ ∧
      Δ.mor₃ ≫ a⟦1⟧' = c ≫ Δ'.mor₃ := by
  let n := Δ.obj₁.level + Δ.obj₂.level + Δ.obj₃.level +
    Δ'.obj₁.level + Δ'.obj₂.level + Δ'.obj₃.level
  have h₁ : Δ.obj₁.level ≤ n := by dsimp [n]; omega
  have h₂ : Δ.obj₂.level ≤ n := by dsimp [n]; omega
  have h₃ : Δ.obj₃.level ≤ n := by dsimp [n]; omega
  have h₁' : Δ'.obj₁.level ≤ n := by dsimp [n]; omega
  have h₂' : Δ'.obj₂.level ≤ n := by dsimp [n]; omega
  have h₃' : Δ'.obj₃.level ≤ n := by dsimp [n]; omega
  have hab' : homEquiv T _ _ n h₁ h₂ Δ.mor₁ ≫ homEquiv T _ _ n h₂ h₂' b =
      homEquiv T _ _ n h₁ h₁' a ≫ homEquiv T _ _ n h₁' h₂' Δ'.mor₁ := by
    rw [← homEquiv_comp T _ _ n h₁ h₂ h₂', ← homEquiv_comp T _ _ n h₁ h₁' h₂', hab]
  obtain ⟨c, hc₂, hc₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism
    (stageTriangle T Δ n h₁ h₂ h₃) (stageTriangle T Δ' n h₁' h₂' h₃')
    ((distinguished_iff T Δ n h₁ h₂ h₃).1 hΔ)
    ((distinguished_iff T Δ' n h₁' h₂' h₃').1 hΔ')
    (homEquiv T _ _ n h₁ h₁' a) (homEquiv T _ _ n h₂ h₂' b) hab'
  change stage T Δ.obj₃ n ⟶ stage T Δ'.obj₃ n at c
  refine ⟨(homEquiv T _ _ n h₃ h₃').symm c, ?_, ?_⟩
  · apply hom_ext T n h₂ h₃'
    rw [homEquiv_comp T _ _ n h₂ h₃ h₃', homEquiv_comp T _ _ n h₂ h₂' h₃',
      Equiv.apply_symm_apply]
    exact hc₂
  · apply hom_ext T (X := Δ.obj₃) (Y := Δ'.obj₁⟦(1 : ℤ)⟧) n h₃ h₁'
    rw [homEquiv_comp T Δ.mor₃ (a⟦(1 : ℤ)⟧') n h₃ h₁ h₁',
      homEquiv_comp T ((homEquiv T _ _ n h₃ h₃').symm c) Δ'.mor₃ n h₃ h₃' h₁',
      Equiv.apply_symm_apply, homEquiv_shift T 1 a n h₁ h₁']
    have he := congrArg (fun f => f ≫ (stageShiftIso T 1 Δ'.obj₁ n).inv) hc₃
    simp only [stageTriangle, Triangle.mk_mor₃, Category.assoc] at he ⊢
    erw [Iso.hom_inv_id, Category.comp_id] at he
    exact he

instance : Pretriangulated (Stabilization T) where
  distinguishedTriangles := {Δ | Distinguished T Δ}
  isomorphic_distinguished _ hΔ _ e := distinguished_of_iso T e.symm hΔ
  contractible_distinguished := contractible_distinguished T
  distinguished_cocone_triangle := distinguished_cocone_triangle T
  rotate_distinguished_triangle := rotate_distinguished_triangle T
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism T

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion followed by realization at the same denominator recovers the original triangle. -/
def stageTriangleAtLevelIso (n : ℕ) (Δ : Triangle C) :
    stageTriangle T ((atLevel T n).mapTriangle.obj Δ) n
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) ≅ Δ :=
  Triangle.isoMk _ _ (atLevelStageIso T n Δ.obj₁) (atLevelStageIso T n Δ.obj₂)
    (atLevelStageIso T n Δ.obj₃)
    (by simp [stageTriangle, homEquiv_atLevel_map, Functor.mapTriangle])
    (by simp [stageTriangle, homEquiv_atLevel_map, Functor.mapTriangle])
    (by
      have hn : n ≤ n := le_rfl
      change (homEquiv T ((atLevel T n).obj Δ.obj₃) ((atLevel T n).obj (Δ.obj₁⟦(1 : ℤ)⟧))
        n hn hn ((atLevel T n).map Δ.mor₃ ≫ 𝟙 _) ≫
          (stageShiftIso T 1 ((atLevel T n).obj Δ.obj₁) n).hom) ≫
            ((atLevelStageIso T n Δ.obj₁).hom)⟦(1 : ℤ)⟧' =
        (atLevelStageIso T n Δ.obj₃).hom ≫ Δ.mor₃
      rw [Category.comp_id, homEquiv_atLevel_map]
      have e (k : ℕ) (hk : k = 0) (A : C) :
          ((iterate T k).commShiftIso (1 : ℤ)).hom.app A ≫
            (eqToHom (congrArg (fun l => (iterate T l).obj A) hk))⟦(1 : ℤ)⟧' =
          eqToHom (congrArg (fun l => (iterate T l).obj (A⟦(1 : ℤ)⟧)) hk) := by
        subst k
        change ((𝟭 C).commShiftIso (1 : ℤ)).hom.app A ≫
          (𝟙 A)⟦(1 : ℤ)⟧' = 𝟙 (A⟦(1 : ℤ)⟧)
        simp
      have he :
          (stageShiftIso T 1 ((atLevel T n).obj Δ.obj₁) n).hom ≫
            ((atLevelStageIso T n Δ.obj₁).hom)⟦(1 : ℤ)⟧' =
          (atLevelStageIso T n (Δ.obj₁⟦(1 : ℤ)⟧)).hom := e _ (Nat.sub_self n) _
      rw [Category.assoc, he]
      simp)

instance atLevel_isTriangulated (n : ℕ) : (atLevel T n).IsTriangulated where
  map_distinguished Δ hΔ :=
    (distinguished_iff T _ n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).2
      ((distinguished_iff_of_iso (stageTriangleAtLevelIso T n Δ)).2 hΔ)

end CategoryTheory.Stabilization
