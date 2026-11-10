/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationComparison

/-!
# Whole comparisons from actual small source models
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace CategoryTheory.Waldhausen.IteratedS

/-- The native model record of an already small Waldhausen category. -/
def smallSourceModel {C : Type w} [SmallCategory C] (W : Structure C) :
    WideSubcategory preservesZero.{w} :=
  ⟨{ Obj := C, waldhausen := W }⟩

/-- The object projection retains the original raw category. -/
theorem smallSourceModel_obj {C : Type w} [SmallCategory C] (W : Structure C) :
    (smallSourceModel W).obj.Obj = C := rfl

/-- The category projection retains the original raw instance. -/
theorem smallSourceModel_category {C : Type w} [SmallCategory C]
    (W : Structure C) :
    (smallSourceModel W).obj.category = inferInstanceAs (SmallCategory C) := rfl

variable {D₀ D₁ D₂ : Type u} [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
variable {C₀ C₁ C₂ : Type (max u v)}
  [SmallCategory C₀] [SmallCategory C₁] [SmallCategory C₂]

/-- Whole composition with raw source category parameters and literal native models. -/
theorem smallSourceEvaluationIso_comp_hom
    (Ws₀ : Structure C₀) (Ws₁ : Structure C₁) (Ws₂ : Structure C₂)
    (W₀ : Structure D₀) (W₁ : Structure D₁) (W₂ : Structure D₂)
    (A : smallSourceModel Ws₀ ⟶ smallSourceModel Ws₁)
    (B : smallSourceModel Ws₁ ⟶ smallSourceModel Ws₂)
    (K : smallSourceModel Ws₀ ⟶ smallSourceModel Ws₂)
    (E₀ : smallSourceModel Ws₀ ⟶ asSmallCategory W₀)
    (E₁ : smallSourceModel Ws₁ ⟶ asSmallCategory W₁)
    (E₂ : (smallSourceModel Ws₂) ⟶ asSmallCategory W₂)
    (P : asSmallCategory W₀ ⟶ asSmallCategory W₁)
    (Q : asSmallCategory W₁ ⟶ asSmallCategory W₂)
    (R : asSmallCategory W₀ ⟶ asSmallCategory W₂)
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂)
    (c : C₀ ⥤ C₂)
    (e₀ : C₀ ⥤ D₀) (e₁ : C₁ ⥤ D₁) (e₂ : C₂ ⥤ D₂)
    (p : D₀ ⥤ D₁) (q : D₁ ⥤ D₂) (r : D₀ ⥤ D₂)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (β : b ⋙ e₂ ≅ e₁ ⋙ q)
    (γ : c ⋙ e₂ ≅ e₀ ⋙ r) (μ : r ≅ p ⋙ q)
    (hA : A.hom.toFunctor = a) (hB : B.hom.toFunctor = b) (hK : K.hom.toFunctor = c)
    (hE₀ : E₀.hom.toFunctor = e₀ ⋙ AsSmall.up)
    (hE₁ : E₁.hom.toFunctor = e₁ ⋙ AsSmall.up)
    (hE₂ : E₂.hom.toFunctor = e₂ ⋙ AsSmall.up)
    (hP : P.hom.toFunctor = asSmallFunctor p)
    (hQ : Q.hom.toFunctor = asSmallFunctor q)
    (hR : R.hom.toFunctor = asSmallFunctor r)
    (hPQ : (P ≫ Q).hom.toFunctor = asSmallFunctor p ⋙ asSmallFunctor q)
    (sα : (A ≫ E₁).hom.toFunctor = a ⋙ (e₁ ⋙ AsSmall.up))
    (tα : (E₀ ≫ P).hom.toFunctor = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor p)
    (sβ : (B ≫ E₂).hom.toFunctor = b ⋙ (e₂ ⋙ AsSmall.up))
    (tβ : (E₁ ≫ Q).hom.toFunctor = (e₁ ⋙ AsSmall.up) ⋙ asSmallFunctor q)
    (sγ : (K ≫ E₂).hom.toFunctor = c ⋙ (e₂ ⋙ AsSmall.up))
    (tγ : (E₀ ≫ R).hom.toFunctor = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor r)
    (hRaw : c ⋙ e₂ = (a ⋙ b) ⋙ e₂) (hModel : K ≫ E₂ = A ≫ (B ≫ E₂))
    (h : ∀ x, γ.hom.app x ≫ μ.hom.app (e₀.obj x) =
      (eqToHom hRaw).app x ≫ β.hom.app (a.obj x) ≫ q.map (α.hom.app x))
    (α₀ : (A ≫ E₁).hom.toFunctor ≅ (E₀ ≫ P).hom.toFunctor)
    (β₀ : (B ≫ E₂).hom.toFunctor ≅ (E₁ ≫ Q).hom.toFunctor)
    (γ₀ : (K ≫ E₂).hom.toFunctor ≅ (E₀ ≫ R).hom.toFunctor)
    (μ₀ : R.hom.toFunctor ≅ (P ≫ Q).hom.toFunctor)
    (eα : α₀ = modelAsSmallEvaluationIso W₀ W₁ A E₀ E₁ P a e₁ e₀ p α sα tα)
    (eβ : β₀ = modelAsSmallEvaluationIso W₁ W₂ B E₁ E₂ Q b e₂ e₁ q β sβ tβ)
    (eγ : γ₀ = modelAsSmallEvaluationIso W₀ W₂ K E₀ E₂ R c e₂ e₀ r γ sγ tγ)
    (eμ : μ₀ = modelAsSmallCompositionIso W₀ W₂ p q r μ
          (F₀ := R.hom.toFunctor) (G₀ := (P ≫ Q).hom.toFunctor) hR
          hPQ) :
    γ₀.hom ≫ modelWhiskerLeft E₀ μ₀.hom =
      modelEqToHom hModel ≫ modelWhiskerLeft A β₀.hom ≫
        modelWhiskerRightAssoc A E₁ E₀ P Q α₀.hom := by
  exact modelEvaluationIso_comp_hom_of_eq W₀ W₁ W₂ A B K E₀ E₁ E₂ P Q R
    a b c e₀ e₁ e₂ p q r α β γ μ hA hB hK hE₀ hE₁ hE₂ hP hQ hR hPQ
    sα tα sβ tβ sγ tγ hRaw hModel h α₀ β₀ γ₀ μ₀ eα eβ eγ eμ

/-- Whole unit with the unchanged native model and raw source category. -/
theorem smallSourceEvaluationIso_id_hom
    (Ws : Structure C₀)
    (W : Structure D₀)
    (A : smallSourceModel Ws ⟶ smallSourceModel Ws)
    (E : smallSourceModel Ws ⟶ asSmallCategory W)
    (P : asSmallCategory W ⟶ asSmallCategory W)
    (a : C₀ ⥤ C₀) (e : C₀ ⥤ D₀) (p : D₀ ⥤ D₀)
    (α : a ⋙ e ≅ e ⋙ p) (δ : p ≅ 𝟭 D₀)
    (hA : A.hom.toFunctor = a) (hE : E.hom.toFunctor = e ⋙ AsSmall.up)
    (hP : P.hom.toFunctor = asSmallFunctor p)
    (sα : (A ≫ E).hom.toFunctor = a ⋙ (e ⋙ AsSmall.up))
    (tα : (E ≫ P).hom.toFunctor = (e ⋙ AsSmall.up) ⋙ asSmallFunctor p)
    (hRaw : a ⋙ e = (𝟭 C₀) ⋙ e) (hModel : A ≫ E = E)
    (h : ∀ x, α.hom.app x ≫ δ.hom.app (e.obj x) = (eqToHom hRaw).app x)
    (α₀ : (A ≫ E).hom.toFunctor ≅ (E ≫ P).hom.toFunctor)
    (δ₀ : P.hom.toFunctor ≅
      (𝟙 (asSmallCategory W) : asSmallCategory W ⟶ asSmallCategory W).hom.toFunctor)
    (eα : α₀ = modelAsSmallEvaluationIso W W A E E P a e e p α sα tα)
    (eδ : δ₀ = modelAsSmallIdentityIso W p δ (F₀ := P.hom.toFunctor)
          (G₀ := (𝟙 (asSmallCategory W) : asSmallCategory W ⟶ asSmallCategory W).hom.toFunctor)
          hP (smallModel_id_toFunctor (asSmallCategory W))) :
    α₀.hom ≫ modelWhiskerLeftId E δ₀.hom = modelEqToHom hModel := by
  exact modelEvaluationIso_id_hom_of_eq W A E P a e p α δ hA hE hP sα tα
    hRaw hModel h α₀ δ₀ eα eδ

end CategoryTheory.Waldhausen.IteratedS
