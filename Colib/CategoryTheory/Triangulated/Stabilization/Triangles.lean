/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Shift
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Triangles at finite common stages -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open Pretriangulated Limits

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) [T.Full] [T.Faithful]
  [HasShift C ℤ] [T.CommShift ℤ]

/-- Realization of a stable triangle at any level bounding its three denominators. -/
def stageTriangle (Δ : Triangle (Stabilization T)) (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n) : Triangle C :=
  Triangle.mk (homEquiv T _ _ n h₁ h₂ Δ.mor₁) (homEquiv T _ _ n h₂ h₃ Δ.mor₂)
    (homEquiv T Δ.obj₃ (Δ.obj₁⟦(1 : ℤ)⟧) n h₃ h₁ Δ.mor₃ ≫ (stageShiftIso T 1 Δ.obj₁ n).hom)

omit [HasShift C ℤ] [T.CommShift ℤ] in
/-- The comparison isomorphism of stages intertwines each realized stable arrow. -/
lemma stageIso_homEquiv {X Y : Stabilization T} (f : X ⟶ Y) {m n : ℕ}
    (hX : X.level ≤ m) (hY : Y.level ≤ m) (h : m ≤ n) :
    (iterate T (n - m)).map (homEquiv T X Y m hX hY f) ≫ (stageIso T Y hY h).hom =
      (stageIso T X hX h).hom ≫
        homEquiv T X Y n (Nat.le_trans hX h) (Nat.le_trans hY h) f := by
  change _ = (stageIso T X hX h).hom ≫
    Hom.toStage f n (Nat.le_trans hX h) (Nat.le_trans hY h)
  rw [← Hom.toStage_trans f hX hY h]
  simp [transition]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of stable triangles, with all its equations, lifts to a common stage. -/
def stageTriangleMap {Δ Δ' : Triangle (Stabilization T)} (φ : Δ ⟶ Δ') (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n)
    (h₁' : Δ'.obj₁.level ≤ n) (h₂' : Δ'.obj₂.level ≤ n) (h₃' : Δ'.obj₃.level ≤ n) :
    stageTriangle T Δ n h₁ h₂ h₃ ⟶ stageTriangle T Δ' n h₁' h₂' h₃' where
  hom₁ := homEquiv T _ _ n h₁ h₁' φ.hom₁
  hom₂ := homEquiv T _ _ n h₂ h₂' φ.hom₂
  hom₃ := homEquiv T _ _ n h₃ h₃' φ.hom₃
  comm₁ := by
    dsimp only [stageTriangle, Triangle.mk_mor₁]
    rw [← homEquiv_comp T _ _ n h₁ h₂ h₂',
      ← homEquiv_comp T _ _ n h₁ h₁' h₂', φ.comm₁]
  comm₂ := by
    dsimp only [stageTriangle, Triangle.mk_mor₂]
    rw [← homEquiv_comp T _ _ n h₂ h₃ h₃',
      ← homEquiv_comp T _ _ n h₂ h₂' h₃', φ.comm₂]
  comm₃ := by
    have e := congrArg (homEquiv T Δ.obj₃ (Δ'.obj₁⟦(1 : ℤ)⟧) n h₃ h₁') φ.comm₃
    rw [homEquiv_comp T Δ.mor₃ (φ.hom₁⟦(1 : ℤ)⟧') n h₃ h₁ h₁',
      homEquiv_comp T φ.hom₃ Δ'.mor₃ n h₃ h₃' h₁',
      homEquiv_shift T 1 φ.hom₁ n h₁ h₁'] at e
    dsimp only [stageTriangle, Triangle.mk_mor₃]
    have he := congrArg (fun f => f ≫ (stageShiftIso T 1 Δ'.obj₁ n).hom) e
    simp only [Category.assoc] at he ⊢
    erw [Iso.inv_hom_id, Category.comp_id] at he
    exact he

/-- Isomorphic stable triangles remain isomorphic at any common level. -/
def stageTriangleIso {Δ Δ' : Triangle (Stabilization T)} (e : Δ ≅ Δ') (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n)
    (h₁' : Δ'.obj₁.level ≤ n) (h₂' : Δ'.obj₂.level ≤ n) (h₃' : Δ'.obj₃.level ≤ n) :
    stageTriangle T Δ n h₁ h₂ h₃ ≅ stageTriangle T Δ' n h₁' h₂' h₃' where
  hom := stageTriangleMap T e.hom n h₁ h₂ h₃ h₁' h₂' h₃'
  inv := stageTriangleMap T e.inv n h₁' h₂' h₃' h₁ h₂ h₃
  hom_inv_id := by
    ext
    · change homEquiv T _ _ n h₁ h₁' _ ≫ homEquiv T _ _ n h₁' h₁ _ = 𝟙 _
      rw [← homEquiv_comp T _ _ n h₁ h₁' h₁, e.hom_inv_id_triangle_hom₁, homEquiv_id]
    · change homEquiv T _ _ n h₂ h₂' _ ≫ homEquiv T _ _ n h₂' h₂ _ = 𝟙 _
      rw [← homEquiv_comp T _ _ n h₂ h₂' h₂, e.hom_inv_id_triangle_hom₂, homEquiv_id]
    · change homEquiv T _ _ n h₃ h₃' _ ≫ homEquiv T _ _ n h₃' h₃ _ = 𝟙 _
      rw [← homEquiv_comp T _ _ n h₃ h₃' h₃, e.hom_inv_id_triangle_hom₃, homEquiv_id]
  inv_hom_id := by
    ext
    · change homEquiv T _ _ n h₁' h₁ _ ≫ homEquiv T _ _ n h₁ h₁' _ = 𝟙 _
      rw [← homEquiv_comp T _ _ n h₁' h₁ h₁', e.inv_hom_id_triangle_hom₁, homEquiv_id]
    · change homEquiv T _ _ n h₂' h₂ _ ≫ homEquiv T _ _ n h₂ h₂' _ = 𝟙 _
      rw [← homEquiv_comp T _ _ n h₂' h₂ h₂', e.inv_hom_id_triangle_hom₂, homEquiv_id]
    · change homEquiv T _ _ n h₃' h₃ _ ≫ homEquiv T _ _ n h₃ h₃' _ = 𝟙 _
      rw [← homEquiv_comp T _ _ n h₃' h₃ h₃', e.inv_hom_id_triangle_hom₃, homEquiv_id]

set_option backward.isDefEq.respectTransparency false in
/-- Increasing a triangle's common stage applies the corresponding iterate of `T`. -/
def stageTriangleTransitionIso (Δ : Triangle (Stabilization T)) {m n : ℕ}
    (h₁ : Δ.obj₁.level ≤ m) (h₂ : Δ.obj₂.level ≤ m) (h₃ : Δ.obj₃.level ≤ m) (h : m ≤ n) :
    (iterate T (n - m)).mapTriangle.obj (stageTriangle T Δ m h₁ h₂ h₃) ≅
      stageTriangle T Δ n (Nat.le_trans h₁ h) (Nat.le_trans h₂ h) (Nat.le_trans h₃ h) :=
  Triangle.isoMk _ _ (stageIso T Δ.obj₁ h₁ h) (stageIso T Δ.obj₂ h₂ h)
    (stageIso T Δ.obj₃ h₃ h)
    (stageIso_homEquiv T Δ.mor₁ h₁ h₂ h)
    (stageIso_homEquiv T Δ.mor₂ h₂ h₃ h) (by
      dsimp only [Functor.mapTriangle, stageTriangle, Triangle.mk_obj₁, Triangle.mk_obj₃,
        Triangle.mk_mor₃]
      rw [Functor.map_comp, Category.assoc, Category.assoc, stageIso_shift_hom T 1 Δ.obj₁ h₁ h]
      rw [← Category.assoc]
      erw [stageIso_homEquiv T Δ.mor₃ h₃ h₁ h, Category.assoc])

section Distinguished

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [T.IsTriangulated]

instance iterate_isTriangulated (n : ℕ) : (iterate T n).IsTriangulated := by
  induction n with
  | zero => change (𝟭 C).IsTriangulated; infer_instance
  | succ n ih => change (iterate T n ⋙ T).IsTriangulated; infer_instance

/-- A stable triangle is distinguished when it is distinguished at a finite common stage. -/
def Distinguished (Δ : Triangle (Stabilization T)) : Prop :=
  ∃ (n : ℕ) (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n),
    stageTriangle T Δ n h₁ h₂ h₃ ∈ distTriang C

/-- Full faithfulness and exactness make the distinguished-triangle test independent of stage. -/
lemma stageTriangle_distinguished_iff (Δ : Triangle (Stabilization T)) {m n : ℕ}
    (h₁ : Δ.obj₁.level ≤ m) (h₂ : Δ.obj₂.level ≤ m) (h₃ : Δ.obj₃.level ≤ m) (h : m ≤ n) :
    stageTriangle T Δ n (Nat.le_trans h₁ h) (Nat.le_trans h₂ h) (Nat.le_trans h₃ h) ∈ distTriang C ↔
      stageTriangle T Δ m h₁ h₂ h₃ ∈ distTriang C := by
  rw [← distinguished_iff_of_iso (stageTriangleTransitionIso T Δ h₁ h₂ h₃ h),
    (iterate T (n - m)).map_distinguished_iff]

/-- Distinguishedness can be tested at every prescribed common finite stage. -/
lemma distinguished_iff (Δ : Triangle (Stabilization T)) (n : ℕ)
    (h₁ : Δ.obj₁.level ≤ n) (h₂ : Δ.obj₂.level ≤ n) (h₃ : Δ.obj₃.level ≤ n) :
    Distinguished T Δ ↔ stageTriangle T Δ n h₁ h₂ h₃ ∈ distTriang C := by
  refine ⟨?_, fun h => ⟨n, h₁, h₂, h₃, h⟩⟩
  rintro ⟨m, hm₁, hm₂, hm₃, hm⟩
  exact (stageTriangle_distinguished_iff T Δ h₁ h₂ h₃ (Nat.le_max_right m n)).1
    ((stageTriangle_distinguished_iff T Δ hm₁ hm₂ hm₃ (Nat.le_max_left m n)).2 hm)

end Distinguished

end CategoryTheory.Stabilization
