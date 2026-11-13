/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Pushout maps with a fixed quotient

In a pushout of an inclusion to a fixed quotient, the intersection with
the inclusion recovers the original collapsed subobject. Cartesian
squares with that subobject therefore retain their exact intersections
after the quotient.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits.Types

/-- Two distinct elements of the same pushout leg become equal only when
both came from elements with the same image in the collapsed object. -/
theorem exists_of_pushout_inl_eq_inl {T A B P : Type u}
    {f : T ⟶ A} {g : T ⟶ B} {i : A ⟶ P} {j : B ⟶ P}
    (s : IsPushout f g i j) (hf : Function.Injective f) {x y : A}
    (hne : x ≠ y) (he : i x = i y) : ∃ a b : T, g a = g b ∧ f a = x ∧ f b = y := by
  let : Mono f := (CategoryTheory.mono_iff_injective f).2 hf
  let t : IsPushout f g (Types.Pushout.inl f g) (Types.Pushout.inr f g) :=
    IsPushout.of_isColimit (Types.Pushout.isColimitCocone f g)
  let e := s.isoIsPushout _ _ t
  have h₀ := ConcreteCategory.congr_hom (s.inl_isoIsPushout_hom _ _ t) x
  have h₁ := ConcreteCategory.congr_hom (s.inl_isoIsPushout_hom _ _ t) y
  have h : Types.Pushout.inl f g x = Types.Pushout.inl f g y :=
    h₀.symm.trans ((congrArg e.hom he).trans h₁)
  have hr := (Types.Pushout.quot_mk_eq_iff f g (Sum.inl x) (Sum.inl y)).1 h
  obtain hxy | ⟨a, b, hab, ha, hb⟩ := (Types.Pushout.inl_rel'_inl_iff f g x y).1 hr
  · exact (hne hxy).elim
  · exact ⟨a, b, hab, ha.symm, hb.symm⟩

variable {T A B P Q K : Type u} {a : T ⟶ A} {b : T ⟶ B} {c : T ⟶ K}
  {i : A ⟶ P} {j : B ⟶ Q} {p : K ⟶ P} {q : K ⟶ Q}
  {f : A ⟶ B} {g : P ⟶ Q}

/-- A map between two pushouts with the same collapsed subobject is a
pullback along the unquotiented map when that map meets the collapsed
subobject in exactly the given source. -/
theorem isPullback_of_pushout_fixed
    (s : IsPushout a c i p) (t : IsPushout b c j q)
    [Mono b] [Mono f]
    (h : IsPullback a (𝟙 T) f b) (w₁ : i ≫ g = f ≫ j) (w₂ : p ≫ g = q) :
    IsPullback i f g j := by
  have t' := Types.isPullback_of_isPushout t (CategoryTheory.injective_of_mono b)
  rw [Types.isPullback_iff]
  refine ⟨w₁, fun x y hxy => CategoryTheory.injective_of_mono f hxy.2, ?_⟩
  intro x y e
  rcases Types.eq_or_eq_of_isPushout s x with ⟨x', rfl⟩ | ⟨k, rfl⟩
  · have e' : j (f x') = j y :=
      (ConcreteCategory.congr_hom w₁ x').symm.trans e
    by_cases hxy : f x' = y
    · exact ⟨x', rfl, hxy⟩
    obtain ⟨t₁, t₂, hc, h₁, h₂⟩ := exists_of_pushout_inl_eq_inl t
      (CategoryTheory.injective_of_mono b) hxy e'
    obtain ⟨x₁, hx₁, hx₂⟩ := Types.exists_of_isPullback h x' t₁ h₁.symm
    refine ⟨a t₂, ?_, ?_⟩
    · have ha : a t₁ = x' := by
        change x₁ = t₁ at hx₂
        rwa [← hx₂]
      rw [← ha]
      have he₁ := ConcreteCategory.congr_hom s.w t₁
      have he₂ := ConcreteCategory.congr_hom s.w t₂
      exact he₂.trans ((congrArg p hc.symm).trans he₁.symm)
    · exact (ConcreteCategory.congr_hom h.w t₂).trans h₂
  · have he : j y = q k := e.symm.trans (ConcreteCategory.congr_hom w₂ k)
    obtain ⟨t₀, ht₁, ht₂⟩ := Types.exists_of_isPullback t' y k he
    refine ⟨a t₀, ?_, ?_⟩
    · exact (ConcreteCategory.congr_hom s.w t₀).trans (congrArg p ht₂)
    · exact (ConcreteCategory.congr_hom h.w t₀).trans ht₁

end CategoryTheory.Limits.Types
