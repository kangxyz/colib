/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderBoundary
import Colib.CategoryTheory.Limits.FixedQuotientPullback
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# The two endpoints of the actual pointed simplicial cylinder

Their product graphs meet exactly on the basepoint interval. Collapsing
that axis leaves their intersection equal to the specified point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- Evaluation of a presheaf at an object and a simplicial degree. -/
abbrev cylinderDegreeEvaluation (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (Cᵒᵖ ⥤ SSet.{w}) ⥤ Type w :=
  (CategoryTheory.evaluation Cᵒᵖ SSet.{w}).obj U ⋙
    (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type w)).obj n

private theorem endpoints_ne (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x y : (cylinderDegreeEvaluation.{w} U n).obj (⊤_ (Cᵒᵖ ⥤ SSet.{w}))) :
    (cylinderDegreeEvaluation U n).map (intervalEndpoint C 0) x ≠
      (cylinderDegreeEvaluation U n).map (intervalEndpoint C 1) y := by
  intro h
  change ((SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ 0).app n) x =
    ((SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ 1).app n) y at h
  rw [SSet.stdSimplex.δ_zero_eq_const, SSet.stdSimplex.δ_one_eq_const] at h
  have e := congrArg (fun t : (Δ[1] : SSet.{w}).obj n => t.down.toOrderHom 0) h
  change (1 : Fin 2) = 0 at e
  exact (show (1 : Fin 2) ≠ 0 by decide) e

/-- The endpoint map into the cylinder product before collapsing its basepoint axis. -/
abbrev endpointGraph (A : PointedSimplicialPresheaf.{w} C) (i : Fin 2) :
    A.right ⟶ A.right ⨯ interval C :=
  prod.lift (𝟙 A.right) (terminal.from A.right ≫ intervalEndpoint C i)

private theorem endpointGraph_axis_pullback (A : PointedSimplicialPresheaf.{w} C) (i : Fin 2) :
    IsPullback A.hom (intervalEndpoint C i) (endpointGraph A i) (intervalAxis A (interval C)) := by
  have hA : A.hom ≫ terminal.from A.right = 𝟙 _ := terminal.hom_ext _ _
  let : Mono A.hom := mono_of_mono_fac hA
  have ht : terminal.from (⊤_ (Cᵒᵖ ⥤ SSet.{w})) = 𝟙 _ := terminal.hom_ext _ _
  refine IsPullback.mk' (by apply prod.hom_ext <;> simp [endpointGraph, intervalAxis, ht]) ?_ ?_
  · intro W f g hf _
    exact (cancel_mono A.hom).1 hf
  · intro T a b h
    refine ⟨terminal.from T, ?_, ?_⟩
    · simpa [endpointGraph, intervalAxis, Category.assoc] using congrArg (· ≫ prod.fst) h.symm
    · simpa [endpointGraph, intervalAxis, Category.assoc] using congrArg (· ≫ prod.snd) h

private theorem endpoint_section_point (A : PointedSimplicialPresheaf.{w} C) (i : Fin 2) :
    A.hom ≫ (cylinderSection A (intervalEndpoint C i)).right =
      (parameterizedCylinder A (interval C)).hom :=
  Under.w _

/-- The two endpoint sections meet exactly at the original basepoint in each degree. -/
theorem endpointPair_isPullback_at (A : PointedSimplicialPresheaf.{w} C)
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    let E := cylinderDegreeEvaluation.{w} U n
    IsPullback (E.map A.hom) (E.map A.hom)
      (E.map (cylinderSection A (intervalEndpoint C 0)).right)
      (E.map (cylinderSection A (intervalEndpoint C 1)).right) := by
  let E := cylinderDegreeEvaluation.{w} U n
  let K := interval.{w} C
  let t := intervalAxis A K
  let q := terminal.from K
  let p := pushout.inl t q
  let e₀ := endpointGraph A 0
  let e₁ := endpointGraph A 1
  let : Unique (E.obj (⊤_ (Cᵒᵖ ⥤ SSet.{w}))) :=
    Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj E _)
  have hT : Function.Injective (E.map t) := by
    have h : t ≫ (prod.snd : A.right ⨯ K ⟶ K) = 𝟙 K := prod.lift_snd _ _
    have hh : E.map t ≫ E.map (prod.snd : A.right ⨯ K ⟶ K) = 𝟙 _ := by
      rw [← E.map_comp, h, E.map_id]
    let : Mono (E.map t) := mono_of_mono_fac hh
    exact CategoryTheory.injective_of_mono (E.map t)
  have s := (IsPushout.of_hasPushout t q).map E
  have h₀ := (endpointGraph_axis_pullback A 0).map E
  have h₁ := (endpointGraph_axis_pullback A 1).map E
  change IsPullback (E.map A.hom) (E.map A.hom)
    (E.map (e₀ ≫ p)) (E.map (e₁ ≫ p))
  rw [E.map_comp, E.map_comp, Types.isPullback_iff]
  refine ⟨?_, fun _ _ _ => Subsingleton.elim _ _, ?_⟩
  · simp only [← E.map_comp]
    exact congrArg E.map ((endpoint_section_point A 0).trans (endpoint_section_point A 1).symm)
  · intro x y eq
    have ee : E.map p (E.map e₀ x) = E.map p (E.map e₁ y) := eq
    have hxy : E.map e₀ x ≠ E.map e₁ y := by
      intro h
      have h' := congrArg (E.map (prod.snd : A.right ⨯ K ⟶ K)) h
      have e₀' : e₀ ≫ (prod.snd : A.right ⨯ K ⟶ K) =
          terminal.from A.right ≫ intervalEndpoint C 0 := prod.lift_snd _ _
      have e₁' : e₁ ≫ (prod.snd : A.right ⨯ K ⟶ K) =
          terminal.from A.right ≫ intervalEndpoint C 1 := prod.lift_snd _ _
      change (E.map e₀ ≫ E.map (prod.snd : A.right ⨯ K ⟶ K)) x =
        (E.map e₁ ≫ E.map (prod.snd : A.right ⨯ K ⟶ K)) y at h'
      rw [← E.map_comp, ← E.map_comp, e₀', e₁', E.map_comp, E.map_comp] at h'
      exact endpoints_ne U n _ _ h'
    obtain ⟨k₀, k₁, _, hx, hy⟩ := Types.exists_of_pushout_inl_eq_inl s hT hxy ee
    obtain ⟨t₀, ht₀, _⟩ := Types.exists_of_isPullback h₀ x k₀ hx.symm
    obtain ⟨t₁, ht₁, _⟩ := Types.exists_of_isPullback h₁ y k₁ hy.symm
    exact ⟨t₀, ht₀, (congrArg (E.map A.hom) (Subsingleton.elim t₀ t₁)).trans ht₁⟩

/-- The underlying pointed coproduct of two copies is the original pushout of their points. -/
theorem endpointCoproduct_isPushout (A : PointedSimplicialPresheaf.{w} C) :
    IsPushout A.hom A.hom (coprod.inl : A ⟶ A ⨿ A).right (coprod.inr : A ⟶ A ⨿ A).right := by
  let i₀ : A ⟶ A ⨿ A := coprod.inl
  let i₁ : A ⟶ A ⨿ A := coprod.inr
  let c : BinaryCofan (Under.mk A.hom) (Under.mk A.hom) := BinaryCofan.mk i₀ i₁
  have h : IsColimit c := coprodIsCoprod A A
  exact IsPushout.of_isColimit (h.pushoutCoconeEquivBinaryCofanInverse)

/-- Each original endpoint is monic after degree evaluation. -/
theorem mono_cylinderSection_at (A : PointedSimplicialPresheaf.{w} C)
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) (i : Fin 2) :
    Mono ((cylinderDegreeEvaluation U n).map (cylinderSection A (intervalEndpoint C i)).right) := by
  let E := cylinderDegreeEvaluation.{w} U n
  let s := cylinderSection A (intervalEndpoint C i)
  have h : s.right ≫ (cylinderProjection A (interval C)).right = 𝟙 _ :=
    congrArg Under.Hom.right (cylinderSection_projection A (intervalEndpoint C i))
  have hr : E.map s.right ≫ E.map (cylinderProjection A (interval C)).right = 𝟙 _ := by
    rw [← E.map_comp, h, E.map_id]
  exact mono_of_mono_fac hr

/-- Both endpoints are included by the original pointed coproduct map, degreewise. -/
theorem mono_simplicialEndpointPair_at (A : PointedSimplicialPresheaf.{w} C)
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    Mono ((cylinderDegreeEvaluation U n).map (simplicialEndpointPair A).right) := by
  let E := cylinderDegreeEvaluation.{w} U n
  let s₀ := cylinderSection A (intervalEndpoint C 0)
  let s₁ := cylinderSection A (intervalEndpoint C 1)
  let i₀ : A ⟶ A ⨿ A := coprod.inl
  let i₁ : A ⟶ A ⨿ A := coprod.inr
  have hsq := (endpointCoproduct_isPushout A).map E
  let : Mono (E.map s₀.right) := mono_cylinderSection_at A U n 0
  change Mono (E.map (simplicialEndpointPair A).right)
  refine Types.mono_of_isPushout_of_isPullback hsq (endpointPair_isPullback_at A U n) ?_ ?_ ?_
  · rw [← E.map_comp]
    exact congrArg E.map (congrArg Under.Hom.right (coprod.inl_desc s₀ s₁))
  · rw [← E.map_comp]
    exact congrArg E.map (congrArg Under.Hom.right (coprod.inr_desc s₀ s₁))
  · intro x y _ _ h
    let : Mono (E.map s₁.right) := mono_cylinderSection_at A U n 1
    exact CategoryTheory.injective_of_mono (E.map s₁.right) h

/-- Both endpoints are included by the original pointed coproduct map. -/
theorem mono_simplicialEndpointPair (A : PointedSimplicialPresheaf.{w} C) :
    Mono (simplicialEndpointPair A) := by
  suffices h : Mono (simplicialEndpointPair A).right from Under.mono_of_mono_right _
  exact (NatTrans.mono_iff_mono_app _).2 fun U =>
    (NatTrans.mono_iff_mono_app _).2 fun n => mono_simplicialEndpointPair_at A U n

end CategoryTheory.PointedSimplicialPresheaf
