/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.SimplicialIntervalBoundary
public import Colib.CategoryTheory.Sites.Simplicial.CylinderParameterMap
public import Colib.CategoryTheory.Sites.Simplicial.SmashHomotopy
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct
import Colib.CategoryTheory.Limits.UnderExponential

/-!
# Extending an actual cylinder homotopy through a cartesian pushout-product

The given unpointed lift extends the original track and the prescribed
endpoints. It descends along the target cylinder's basepoint axis because
it extends the original track along the pointed map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- The actual cartesian pushout-product lifting test extends a pointed
cylinder homotopy with the specified endpoints. -/
theorem cylinderHomotopic_of_pushoutProduct_lift
    [MonoidalClosed (Cᵒᵖ ⥤ SSet.{w})]
    {X Y E : PointedSimplicialPresheaf.{w} C} {i : X ⟶ Y}
    (hl : HasLiftingProperty
      (Arrow.mk i.right □ Arrow.mk (simplicialIntervalBoundary.{w} C)).hom (terminal.from E.right))
    {f g : Y ⟶ E} (hfg : CylinderHomotopic (i ≫ f) (i ≫ g)) :
    CylinderHomotopic f g := by
  obtain ⟨H, h₀, h₁⟩ := hfg
  let K := interval.{w} C
  let T := (⊤_ (Cᵒᵖ ⥤ SSet.{w}))
  let d := simplicialIntervalBoundary.{w} C
  let F := curriedTensor (Cᵒᵖ ⥤ SSet.{w})
  let q := Functor.PushoutObjObj.ofHasPushout F i.right d
  let k := (tensorProductIso X.right K).hom ≫ cylinderProductLeg X K ≫ H.right
  let P := tensorLeft Y.right
  let : P.IsLeftAdjoint := (ihom.adjunction Y.right).isLeftAdjoint
  let c := PreservesColimitPair.iso P T T
  let p : Y.right ⊗ (T ⨿ T) ⟶ E.right :=
    c.inv ≫ coprod.desc (CartesianMonoidalCategory.fst Y.right T ≫ f.right)
      (CartesianMonoidalCategory.fst Y.right T ≫ g.right)
  have hp₀ : (Y.right ◁ (coprod.inl : T ⟶ T ⨿ T)) ≫ p =
      CartesianMonoidalCategory.fst Y.right T ≫ f.right := by
    have h : coprod.inl ≫ c.hom = Y.right ◁ (coprod.inl : T ⟶ T ⨿ T) :=
      inl_coprodComparison P T T
    dsimp only [p]
    rw [← h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]
  have hp₁ : (Y.right ◁ (coprod.inr : T ⟶ T ⨿ T)) ≫ p =
      CartesianMonoidalCategory.fst Y.right T ≫ g.right := by
    have h : coprod.inr ≫ c.hom = Y.right ◁ (coprod.inr : T ⟶ T ⨿ T) :=
      inr_coprodComparison P T T
    dsimp only [p]
    rw [← h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]
  have graph (A : Cᵒᵖ ⥤ SSet.{w}) (a : Fin 2) :
      (A ◁ intervalEndpoint C a) ≫ (tensorProductIso A K).hom =
        CartesianMonoidalCategory.fst A T ≫
          prod.lift (𝟙 A) (terminal.from A ≫ intervalEndpoint C a) := by
    apply prod.hom_ext
    · rw [Category.assoc, tensorProductIso_hom_fst,
        CartesianMonoidalCategory.whiskerLeft_fst, Category.assoc, prod.lift_fst, Category.comp_id]
    · simp only [Category.assoc, tensorProductIso_hom_snd,
        CartesianMonoidalCategory.whiskerLeft_snd, prod.lift_snd]
      exact congrArg (· ≫ intervalEndpoint C a) (terminalIsTerminal.hom_ext
        (CartesianMonoidalCategory.snd A T)
        (CartesianMonoidalCategory.fst A T ≫ terminal.from A))
  have hleg (a : Fin 2) (m : Y ⟶ E)
      (hm : cylinderSection X (intervalEndpoint C a) ≫ H = i ≫ m) :
      (X.right ◁ intervalEndpoint C a) ≫ k =
        CartesianMonoidalCategory.fst X.right T ≫ i.right ≫ m.right := by
    change (X.right ◁ intervalEndpoint C a) ≫
      (tensorProductIso X.right K).hom ≫ cylinderProductLeg X K ≫ H.right = _
    rw [reassoc_of% (graph X.right a), ← Category.assoc _ _ H.right,
      ← cylinderSection_right_productLeg]
    exact congrArg (CartesianMonoidalCategory.fst X.right T ≫ ·)
      (congrArg Under.Hom.right hm)
  have hw : (i.right ▷ (T ⨿ T)) ≫ p = (X.right ◁ d) ≫ k := by
    let P' := tensorLeft X.right
    let : P'.IsLeftAdjoint := (ihom.adjunction X.right).isLeftAdjoint
    have h₀d : (coprod.inl : T ⟶ T ⨿ T) ≫ d = intervalEndpoint C 0 := coprod.inl_desc _ _
    have h₁d : (coprod.inr : T ⟶ T ⨿ T) ≫ d = intervalEndpoint C 1 := coprod.inr_desc _ _
    apply (cancel_epi (PreservesColimitPair.iso P' T T).hom).1
    apply coprod.hom_ext
    · simp only [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc]
      change (X.right ◁ (coprod.inl : T ⟶ T ⨿ T)) ≫ (i.right ▷ (T ⨿ T)) ≫ p =
        (X.right ◁ (coprod.inl : T ⟶ T ⨿ T)) ≫ (X.right ◁ d) ≫ k
      rw [whisker_exchange_assoc, hp₀, ← whiskerLeft_comp_assoc, h₀d,
        hleg 0 f h₀, CartesianMonoidalCategory.whiskerRight_fst_assoc]
    · simp only [PreservesColimitPair.iso_hom, inr_coprodComparison_assoc]
      change (X.right ◁ (coprod.inr : T ⟶ T ⨿ T)) ≫ (i.right ▷ (T ⨿ T)) ≫ p =
        (X.right ◁ (coprod.inr : T ⟶ T ⨿ T)) ≫ (X.right ◁ d) ≫ k
      rw [whisker_exchange_assoc, hp₁, ← whiskerLeft_comp_assoc, h₁d,
        hleg 1 g h₁, CartesianMonoidalCategory.whiskerRight_fst_assoc]
  let a := q.isPushout.desc p k hw
  let sq : CommSq a q.ι (terminal.from E.right) (terminal.from (Y.right ⊗ K)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let : HasLiftingProperty q.ι (terminal.from E.right) := hl
  let b := sq.lift
  have hb₀ : (Y.right ◁ d) ≫ b = p := by
    have h : q.inl ≫ q.ι = Y.right ◁ d := q.inl_ι
    rw [← h, Category.assoc, sq.fac_left]
    exact q.isPushout.inl_desc _ _ _
  have hb₁ : (i.right ▷ K) ≫ b = k := by
    have h : q.inr ≫ q.ι = i.right ▷ K := q.inr_ι
    rw [← h, Category.assoc, sq.fac_left]
    exact q.isPushout.inr_desc _ _ _
  let B := (tensorProductIso Y.right K).inv ≫ b
  have hB : prod.map i.right (𝟙 K) ≫ B = cylinderProductLeg X K ≫ H.right := by
    apply (cancel_epi (tensorProductIso X.right K).hom).1
    change (tensorProductIso X.right K).hom ≫ prod.map i.right (𝟙 K) ≫
      (tensorProductIso Y.right K).inv ≫ b = _
    rw [← tensorProductIso_naturality_assoc, Iso.hom_inv_id_assoc, tensorHom_id, hb₁]
  have ha : intervalAxis X K ≫ prod.map i.right (𝟙 K) = intervalAxis Y K := by
    apply prod.hom_ext <;> simp [Category.assoc, intervalAxis, Under.w i]
  have hpoint : intervalAxis Y K ≫ B = terminal.from K ≫ E.hom := by
    rw [← ha, Category.assoc, hB, intervalAxis_cylinderProductLeg_assoc, Under.w H]
  let H' : parameterizedCylinder Y K ⟶ E :=
    Under.homMk (pushout.desc B E.hom hpoint) (pushout.inr_desc _ _ _)
  have hb (t : Fin 2) (m : Y ⟶ E) (j : T ⟶ T ⨿ T) (hj : j ≫ d = intervalEndpoint C t)
      (hpj : (Y.right ◁ j) ≫ p = CartesianMonoidalCategory.fst Y.right T ≫ m.right) :
      cylinderSection Y (intervalEndpoint C t) ≫ H' = m := by
    have e : (Y.right ◁ intervalEndpoint C t) ≫ b =
        CartesianMonoidalCategory.fst Y.right T ≫ m.right := by
      rw [← hj, whiskerLeft_comp, Category.assoc, hb₀, hpj]
    apply Under.UnderMorphism.ext
    change (prod.lift (𝟙 Y.right) (terminal.from Y.right ≫ intervalEndpoint C t) ≫
      cylinderProductLeg Y K) ≫ H'.right = m.right
    rw [Category.assoc, show cylinderProductLeg Y K ≫ H'.right = B from pushout.inl_desc ..]
    let π := CartesianMonoidalCategory.fst Y.right T
    let : Epi π := epi_of_epi_fac
      (CartesianMonoidalCategory.lift_fst (𝟙 Y.right) (terminal.from Y.right))
    apply (cancel_epi π).1
    change π ≫ prod.lift (𝟙 Y.right) (terminal.from Y.right ≫ intervalEndpoint C t) ≫
      (tensorProductIso Y.right K).inv ≫ b = π ≫ m.right
    rw [← reassoc_of% (graph Y.right t), Iso.hom_inv_id_assoc, e]
  exact ⟨H', hb 0 f coprod.inl (coprod.inl_desc _ _) hp₀,
    hb 1 g coprod.inr (coprod.inr_desc _ _) hp₁⟩

end CategoryTheory.PointedSimplicialPresheaf
