/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparisonIso
/-!
# Whole coherence of native small-model evaluation comparisons

Evaluation into the actual small model lifts a mixed-universe comparison only once.
The composition and unit equations below retain the original source equality and all
endpoint transports. Their native forms consume proved functor projections and actual
pointwise comparison equations, and conclude equality of whole natural transformations.
They do not infer coherence from equality on homotopy groups.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u v u₁ v₁
namespace CategoryTheory.Waldhausen.IteratedS
variable {C₀ C₁ C₂ : Type u₁} [Category.{v₁} C₀] [Category.{v₁} C₁] [Category.{v₁} C₂]
variable {D₀ D₁ D₂ : Type u} [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]

/-- asSmallEvaluationWhiskerIso comp hom for the actual once-lifted evaluation comparison. -/
theorem asSmallEvaluationWhiskerIso_comp_hom
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₀ ⥤ C₂)
    (e₀ : C₀ ⥤ D₀) (e₁ : C₁ ⥤ D₁) (e₂ : C₂ ⥤ D₂)
    (p : D₀ ⥤ D₁) (q : D₁ ⥤ D₂) (r : D₀ ⥤ D₂)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (β : b ⋙ e₂ ≅ e₁ ⋙ q)
    (γ : c ⋙ e₂ ≅ e₀ ⋙ r) (μ : r ≅ p ⋙ q)
    (hRaw : c ⋙ e₂ = (a ⋙ b) ⋙ e₂)
    (hSmall : c ⋙ (e₂ ⋙ AsSmall.up) = a ⋙ (b ⋙ (e₂ ⋙ AsSmall.up)))
    (h : γ.hom ≫ whiskerLeft e₀ μ.hom =
      eqToHom hRaw ≫ whiskerLeft a β.hom ≫ whiskerRight α.hom q) :
    (asSmallEvaluationWhiskerIso c e₂ e₀ r γ).hom ≫
      whiskerLeft (e₀ ⋙ AsSmall.up) (asSmallCompositionIso p q r μ).hom =
    eqToHom hSmall ≫
      whiskerLeft a (asSmallEvaluationWhiskerIso b e₂ e₁ q β).hom ≫
      whiskerRight (asSmallEvaluationWhiskerIso a e₁ e₀ p α).hom (asSmallFunctor q) := by
  apply NatTrans.ext
  funext x
  have h₁ := congrArg (fun η : c ⋙ e₂ ⟶ e₀ ⋙ (p ⋙ q) => η.app x) h
  have h₂ := congrArg (AsSmall.up : D₂ ⥤ AsSmall.{0} D₂).map h₁
  change (AsSmall.up : D₂ ⥤ AsSmall.{0} D₂).map (γ.hom.app x) ≫
      AsSmall.up.map (μ.hom.app (e₀.obj x)) =
    (eqToHom hSmall).app x ≫ AsSmall.up.map (β.hom.app (a.obj x)) ≫
      AsSmall.up.map (q.map (α.hom.app x))
  simpa only [Functor.map_comp, eqToHom_map, eqToHom_app, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app] using h₂

/-- asSmallEvaluationWhiskerIso id hom for the actual once-lifted evaluation comparison. -/
theorem asSmallEvaluationWhiskerIso_id_hom
    (a : C₀ ⥤ C₀) (e : C₀ ⥤ D₀) (p : D₀ ⥤ D₀)
    (α : a ⋙ e ≅ e ⋙ p) (δ : p ≅ 𝟭 D₀)
    (hRaw : a ⋙ e = e)
    (hSmall : a ⋙ (e ⋙ AsSmall.up) = e ⋙ AsSmall.up)
    (h : α.hom ≫ whiskerLeft e δ.hom = eqToHom hRaw) :
    (asSmallEvaluationWhiskerIso a e e p α).hom ≫
      whiskerLeft (e ⋙ AsSmall.up) (asSmallIdentityIso p δ).hom =
        eqToHom hSmall := by
  apply NatTrans.ext
  funext x
  have h₁ := congrArg (fun η : a ⋙ e ⟶ e => η.app x) h
  have h₂ := congrArg (AsSmall.up : D₀ ⥤ AsSmall.{0} D₀).map h₁
  change (AsSmall.up : D₀ ⥤ AsSmall.{0} D₀).map (α.hom.app x) ≫
      AsSmall.up.map (δ.hom.app (e.obj x)) = (eqToHom hSmall).app x
  simpa only [Functor.map_comp, eqToHom_map, eqToHom_app, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app] using h₂

/-- transportedAsSmallEvaluationIso for the actual once-lifted evaluation comparison. -/
def transportedAsSmallEvaluationIso
    (a : C₀ ⥤ C₁) (e₁ : C₁ ⥤ D₁) (e₀ : C₀ ⥤ D₀) (p : D₀ ⥤ D₁)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p)
    {A : C₀ ⥤ C₁} {E₁ : C₁ ⥤ AsSmall.{0} D₁}
    {E₀ : C₀ ⥤ AsSmall.{0} D₀} {P : AsSmall.{0} D₀ ⥤ AsSmall.{0} D₁}
    (hSource : A ⋙ E₁ = a ⋙ (e₁ ⋙ AsSmall.up))
    (hTarget : E₀ ⋙ P = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor p) :
    A ⋙ E₁ ≅ E₀ ⋙ P :=
  Functor.transportIso hSource hTarget (asSmallEvaluationWhiskerIso a e₁ e₀ p α)

/-- transportedAsSmallEvaluationIso comp hom for the actual once-lifted evaluation comparison. -/
theorem transportedAsSmallEvaluationIso_comp_hom
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₀ ⥤ C₂)
    (e₀ : C₀ ⥤ D₀) (e₁ : C₁ ⥤ D₁) (e₂ : C₂ ⥤ D₂)
    (p : D₀ ⥤ D₁) (q : D₁ ⥤ D₂) (r : D₀ ⥤ D₂)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (β : b ⋙ e₂ ≅ e₁ ⋙ q)
    (γ : c ⋙ e₂ ≅ e₀ ⋙ r) (μ : r ≅ p ⋙ q)
    {A : C₀ ⥤ C₁} {B : C₁ ⥤ C₂} {K : C₀ ⥤ C₂}
    {E₀ : C₀ ⥤ AsSmall.{0} D₀} {E₁ : C₁ ⥤ AsSmall.{0} D₁}
    {E₂ : C₂ ⥤ AsSmall.{0} D₂}
    {P : AsSmall.{0} D₀ ⥤ AsSmall.{0} D₁}
    {Q : AsSmall.{0} D₁ ⥤ AsSmall.{0} D₂}
    {R : AsSmall.{0} D₀ ⥤ AsSmall.{0} D₂}
    (hA : A = a) (hB : B = b) (hK : K = c)
    (hE₀ : E₀ = e₀ ⋙ AsSmall.up) (hE₁ : E₁ = e₁ ⋙ AsSmall.up)
    (hE₂ : E₂ = e₂ ⋙ AsSmall.up)
    (hP : P = asSmallFunctor p) (hQ : Q = asSmallFunctor q) (hR : R = asSmallFunctor r)
    (sα : A ⋙ E₁ = a ⋙ (e₁ ⋙ AsSmall.up))
    (tα : E₀ ⋙ P = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor p)
    (sβ : B ⋙ E₂ = b ⋙ (e₂ ⋙ AsSmall.up))
    (tβ : E₁ ⋙ Q = (e₁ ⋙ AsSmall.up) ⋙ asSmallFunctor q)
    (sγ : K ⋙ E₂ = c ⋙ (e₂ ⋙ AsSmall.up))
    (tγ : E₀ ⋙ R = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor r)
    (hRaw : c ⋙ e₂ = (a ⋙ b) ⋙ e₂) (hModel : K ⋙ E₂ = A ⋙ (B ⋙ E₂))
    (h : γ.hom ≫ whiskerLeft e₀ μ.hom =
      eqToHom hRaw ≫ whiskerLeft a β.hom ≫ whiskerRight α.hom q) :
    (transportedAsSmallEvaluationIso c e₂ e₀ r γ sγ tγ).hom ≫
      whiskerLeft E₀
        (Functor.transportIso hR (congrArg₂ (fun f g => f ⋙ g) hP hQ)
          (asSmallCompositionIso p q r μ)).hom =
    eqToHom hModel ≫
      whiskerLeft A (transportedAsSmallEvaluationIso b e₂ e₁ q β sβ tβ).hom ≫
      whiskerRight (transportedAsSmallEvaluationIso a e₁ e₀ p α sα tα).hom Q := by
  subst A; subst B; subst K; subst E₀; subst E₁; subst E₂; subst P; subst Q; subst R
  simpa only [transportedAsSmallEvaluationIso, Functor.transportIso_hom, eqToHom_refl,
    Category.id_comp, Category.comp_id] using
      asSmallEvaluationWhiskerIso_comp_hom a b c e₀ e₁ e₂ p q r α β γ μ hRaw hModel h

/-- transportedAsSmallEvaluationIso id hom for the actual once-lifted evaluation comparison. -/
theorem transportedAsSmallEvaluationIso_id_hom
    (a : C₀ ⥤ C₀) (e : C₀ ⥤ D₀) (p : D₀ ⥤ D₀)
    (α : a ⋙ e ≅ e ⋙ p) (δ : p ≅ 𝟭 D₀)
    {A : C₀ ⥤ C₀} {E : C₀ ⥤ AsSmall.{0} D₀}
    {P : AsSmall.{0} D₀ ⥤ AsSmall.{0} D₀}
    (hA : A = a) (hE : E = e ⋙ AsSmall.up) (hP : P = asSmallFunctor p)
    (sα : A ⋙ E = a ⋙ (e ⋙ AsSmall.up))
    (tα : E ⋙ P = (e ⋙ AsSmall.up) ⋙ asSmallFunctor p)
    (hRaw : a ⋙ e = e) (hModel : A ⋙ E = E)
    (h : α.hom ≫ whiskerLeft e δ.hom = eqToHom hRaw) :
    (transportedAsSmallEvaluationIso a e e p α sα tα).hom ≫
      whiskerLeft E (Functor.transportIso hP rfl (asSmallIdentityIso p δ)).hom =
        eqToHom hModel := by
  subst A; subst E; subst P
  simpa only [transportedAsSmallEvaluationIso, Functor.transportIso_hom,
    eqToHom_refl, Category.id_comp, Category.comp_id] using
      asSmallEvaluationWhiskerIso_id_hom a e p α δ hRaw hModel h

/-- evaluationComposition of app for the actual once-lifted evaluation comparison. -/
theorem evaluationComposition_of_app
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₀ ⥤ C₂)
    (e₀ : C₀ ⥤ D₀) (e₁ : C₁ ⥤ D₁) (e₂ : C₂ ⥤ D₂)
    (p : D₀ ⥤ D₁) (q : D₁ ⥤ D₂) (r : D₀ ⥤ D₂)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (β : b ⋙ e₂ ≅ e₁ ⋙ q)
    (γ : c ⋙ e₂ ≅ e₀ ⋙ r) (μ : r ≅ p ⋙ q)
    (hRaw : c ⋙ e₂ = (a ⋙ b) ⋙ e₂)
    (h : ∀ x, γ.hom.app x ≫ μ.hom.app (e₀.obj x) =
      (eqToHom hRaw).app x ≫ β.hom.app (a.obj x) ≫ q.map (α.hom.app x)) :
    γ.hom ≫ whiskerLeft e₀ μ.hom =
      eqToHom hRaw ≫ whiskerLeft a β.hom ≫ whiskerRight α.hom q := by
  apply NatTrans.ext
  funext x
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] using h x

/-- evaluationIdentity of app for the actual once-lifted evaluation comparison. -/
theorem evaluationIdentity_of_app
    (a : C₀ ⥤ C₀) (e : C₀ ⥤ D₀) (p : D₀ ⥤ D₀)
    (α : a ⋙ e ≅ e ⋙ p) (δ : p ≅ 𝟭 D₀) (hRaw : a ⋙ e = e)
    (h : ∀ x, α.hom.app x ≫ δ.hom.app (e.obj x) = (eqToHom hRaw).app x) :
    α.hom ≫ whiskerLeft e δ.hom = eqToHom hRaw := by
  apply NatTrans.ext
  funext x
  simpa only [NatTrans.comp_app, whiskerLeft_app] using h x

section NativeModels
open SmallWaldhausenCategory
variable {V₀ V₁ V₂ : WideSubcategory preservesZero.{max u v}}


/-- modelEvaluationSource toFunctor for the actual once-lifted evaluation comparison. -/
theorem modelEvaluationSource_toFunctor
    (W : Structure D₁) (A : V₀ ⟶ V₁) (E : V₁ ⟶ asSmallCategory W)
    (a : V₀.obj.Obj ⥤ V₁.obj.Obj) (e : V₁.obj.Obj ⥤ D₁)
    (hA : A.hom.toFunctor = a) (hE : E.hom.toFunctor = e ⋙ AsSmall.up) :
    (A ≫ E).hom.toFunctor = a ⋙ (e ⋙ AsSmall.up) :=
  (smallModel_comp_toFunctor A E).trans (congrArg₂ (fun f g => f ⋙ g) hA hE)

/-- modelEvaluationTarget toFunctor for the actual once-lifted evaluation comparison. -/
theorem modelEvaluationTarget_toFunctor
    (W₀ : Structure D₀) (W₁ : Structure D₁)
    (E : V₀ ⟶ asSmallCategory W₀) (P : asSmallCategory W₀ ⟶ asSmallCategory W₁)
    (e : V₀.obj.Obj ⥤ D₀) (p : D₀ ⥤ D₁)
    (hE : E.hom.toFunctor = e ⋙ AsSmall.up) (hP : P.hom.toFunctor = asSmallFunctor p) :
    (E ≫ P).hom.toFunctor = (e ⋙ AsSmall.up) ⋙ asSmallFunctor p :=
  (smallModel_comp_toFunctor E P).trans (congrArg₂ (fun f g => f ⋙ g) hE hP)

/-- Evaluation comparison between native model arrows with explicit endpoint transports. -/
def modelAsSmallEvaluationIso
    (W₀ : Structure D₀) (W₁ : Structure D₁)
    (A : V₀ ⟶ V₁) (E₀ : V₀ ⟶ asSmallCategory W₀)
    (E₁ : V₁ ⟶ asSmallCategory W₁) (P : asSmallCategory W₀ ⟶ asSmallCategory W₁)
    (a : V₀.obj.Obj ⥤ V₁.obj.Obj) (e₁ : V₁.obj.Obj ⥤ D₁)
    (e₀ : V₀.obj.Obj ⥤ D₀) (p : D₀ ⥤ D₁) (α : a ⋙ e₁ ≅ e₀ ⋙ p)
    (hSource : (A ≫ E₁).hom.toFunctor = a ⋙ (e₁ ⋙ AsSmall.up))
    (hTarget : (E₀ ≫ P).hom.toFunctor = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor p) :
    (A ≫ E₁).hom.toFunctor ≅ (E₀ ≫ P).hom.toFunctor :=
  transportedAsSmallEvaluationIso a e₁ e₀ p α hSource hTarget

/-- Whole native composition equation induced by the original pointwise comparison equation. -/
theorem modelAsSmallEvaluationIso_comp_hom
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
      (eqToHom hRaw).app x ≫ β.hom.app (a.obj x) ≫ q.map (α.hom.app x)) :
    (modelAsSmallEvaluationIso W₀ W₂ K E₀ E₂ R c e₂ e₀ r γ sγ tγ).hom ≫
      whiskerLeft E₀.hom.toFunctor
        (modelAsSmallCompositionIso W₀ W₂ p q r μ
          (F₀ := R.hom.toFunctor) (G₀ := (P ≫ Q).hom.toFunctor) hR
          hPQ).hom =
    eqToHom (congrArg (fun k : V₀ ⟶ asSmallCategory W₂ => k.hom.toFunctor) hModel) ≫
      whiskerLeft A.hom.toFunctor
        (modelAsSmallEvaluationIso W₁ W₂ B E₁ E₂ Q b e₂ e₁ q β sβ tβ).hom ≫
      whiskerRight (modelAsSmallEvaluationIso W₀ W₁ A E₀ E₁ P a e₁ e₀ p α sα tα).hom
        Q.hom.toFunctor := by
  exact transportedAsSmallEvaluationIso_comp_hom a b c e₀ e₁ e₂ p q r α β γ μ
    hA hB hK hE₀ hE₁ hE₂ hP hQ hR sα tα sβ tβ sγ tγ hRaw
    (congrArg (fun k : V₀ ⟶ asSmallCategory W₂ => k.hom.toFunctor) hModel)
    (evaluationComposition_of_app a b c e₀ e₁ e₂ p q r α β γ μ hRaw h)

/-- Whole native unit equation induced by the original pointwise unit equation. -/
theorem modelAsSmallEvaluationIso_id_hom
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
    (h : ∀ x, α.hom.app x ≫ δ.hom.app (e.obj x) = (eqToHom hRaw).app x) :
    (modelAsSmallEvaluationIso W W A E E P a e e p α sα tα).hom ≫
      whiskerLeft E.hom.toFunctor
        (modelAsSmallIdentityIso W p δ (F₀ := P.hom.toFunctor)
          (G₀ := (𝟙 (asSmallCategory W) : asSmallCategory W ⟶ asSmallCategory W).hom.toFunctor)
          hP (smallModel_id_toFunctor (asSmallCategory W))).hom =
      eqToHom (congrArg (fun k : V₀ ⟶ asSmallCategory W => k.hom.toFunctor) hModel) := by
  exact transportedAsSmallEvaluationIso_id_hom a e p α δ hA hE hP sα tα hRaw
    (congrArg (fun k : V₀ ⟶ asSmallCategory W => k.hom.toFunctor) hModel)
    (evaluationIdentity_of_app a e p α δ hRaw h)
end NativeModels

end CategoryTheory.Waldhausen.IteratedS
