/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationCoherence
public import Colib.KTheory.Waldhausen.Iterated.SmallModelTransformations

/-!
# Whole evaluation equations for specified native comparison isomorphisms

Proved constructor equalities identify the supplied comparisons with the actual lifted
comparisons. The conclusions retain the supplied native isomorphisms, while all raw
component equations and source transports remain explicit premises.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
variable {D₀ D₁ D₂ : Type u} [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
variable {V₀ V₁ V₂ : WideSubcategory preservesZero.{max u v}}

/-- Whole composition for specified, provably equal native comparisons. -/
theorem modelEvaluationIso_comp_hom_of_eq
    (W₀ : Structure D₀) (W₁ : Structure D₁) (W₂ : Structure D₂)
    (A : V₀ ⟶ V₁) (B : V₁ ⟶ V₂) (K : V₀ ⟶ V₂)
    (E₀ : V₀ ⟶ asSmallCategory W₀) (E₁ : V₁ ⟶ asSmallCategory W₁)
    (E₂ : V₂ ⟶ asSmallCategory W₂)
    (P : asSmallCategory W₀ ⟶ asSmallCategory W₁)
    (Q : asSmallCategory W₁ ⟶ asSmallCategory W₂)
    (R : asSmallCategory W₀ ⟶ asSmallCategory W₂)
    (a : V₀.obj.Obj ⥤ V₁.obj.Obj) (b : V₁.obj.Obj ⥤ V₂.obj.Obj)
    (c : V₀.obj.Obj ⥤ V₂.obj.Obj)
    (e₀ : V₀.obj.Obj ⥤ D₀) (e₁ : V₁.obj.Obj ⥤ D₁) (e₂ : V₂.obj.Obj ⥤ D₂)
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
  subst α₀; subst β₀; subst γ₀; subst μ₀
  simpa only [modelWhiskerLeft_eq, modelWhiskerRightAssoc_eq, modelEqToHom_eq] using
    modelAsSmallEvaluationIso_comp_hom W₀ W₁ W₂ A B K E₀ E₁ E₂ P Q R
    a b c e₀ e₁ e₂ p q r α β γ μ hA hB hK hE₀ hE₁ hE₂ hP hQ hR hPQ
    sα tα sβ tβ sγ tγ hRaw hModel h

/-- Whole unit for specified, provably equal native comparisons. -/
theorem modelEvaluationIso_id_hom_of_eq
    (W : Structure D₀)
    (A : V₀ ⟶ V₀) (E : V₀ ⟶ asSmallCategory W)
    (P : asSmallCategory W ⟶ asSmallCategory W)
    (a : V₀.obj.Obj ⥤ V₀.obj.Obj) (e : V₀.obj.Obj ⥤ D₀) (p : D₀ ⥤ D₀)
    (α : a ⋙ e ≅ e ⋙ p) (δ : p ≅ 𝟭 D₀)
    (hA : A.hom.toFunctor = a) (hE : E.hom.toFunctor = e ⋙ AsSmall.up)
    (hP : P.hom.toFunctor = asSmallFunctor p)
    (sα : (A ≫ E).hom.toFunctor = a ⋙ (e ⋙ AsSmall.up))
    (tα : (E ≫ P).hom.toFunctor = (e ⋙ AsSmall.up) ⋙ asSmallFunctor p)
    (hRaw : a ⋙ e = e) (hModel : A ≫ E = E)
    (h : ∀ x, α.hom.app x ≫ δ.hom.app (e.obj x) = (eqToHom hRaw).app x)
    (α₀ : (A ≫ E).hom.toFunctor ≅ (E ≫ P).hom.toFunctor)
    (δ₀ : P.hom.toFunctor ≅
      (𝟙 (asSmallCategory W) : asSmallCategory W ⟶ asSmallCategory W).hom.toFunctor)
    (eα : α₀ = modelAsSmallEvaluationIso W W A E E P a e e p α sα tα)
    (eδ : δ₀ = modelAsSmallIdentityIso W p δ (F₀ := P.hom.toFunctor)
          (G₀ := (𝟙 (asSmallCategory W) : asSmallCategory W ⟶ asSmallCategory W).hom.toFunctor)
          hP (smallModel_id_toFunctor (asSmallCategory W))) :
    α₀.hom ≫ modelWhiskerLeftId E δ₀.hom = modelEqToHom hModel := by
  subst α₀; subst δ₀
  simpa only [modelWhiskerLeftId_eq, modelEqToHom_eq] using
    modelAsSmallEvaluationIso_id_hom W A E P a e p α δ hA hE hP sα tα
    hRaw hModel h

end CategoryTheory.Waldhausen.IteratedS
