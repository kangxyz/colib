/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderEndpointMono
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# The two endpoints of the unpointed simplicial interval

The two actual constant endpoint maps have disjoint images in each
degree. Their coproduct is monic in the presheaf category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- The unpointed boundary map of the original constant simplicial interval. -/
def simplicialIntervalBoundary :
    (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⨿ (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ interval C :=
  coprod.desc (intervalEndpoint C 0) (intervalEndpoint C 1)

/-- The coproduct of the two actual simplicial endpoints is monic. -/
theorem mono_simplicialIntervalBoundary : Mono (simplicialIntervalBoundary.{w} C) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun U =>
    (NatTrans.mono_iff_mono_app _).2 fun n => ?_
  let E := cylinderDegreeEvaluation.{w} U n
  let T := (⊤_ (Cᵒᵖ ⥤ SSet.{w}))
  let e := Types.binaryCoproductIso (E.obj T) (E.obj T)
  let d := PreservesColimitPair.iso E T T
  let : Unique (E.obj T) :=
    Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj E _)
  let f := E.map (simplicialIntervalBoundary.{w} C)
  have h₀ (x : E.obj T) : f (d.hom (e.inv (.inl x))) = E.map (intervalEndpoint C 0) x := by
    have h : (↾Sum.inl) ≫ e.inv ≫ d.hom ≫ f = E.map (intervalEndpoint C 0) := by
      rw [← Category.assoc _ e.inv, Types.binaryCoproductIso_inl_comp_inv,
        PreservesColimitPair.iso_hom,
        inl_coprodComparison_assoc, ← E.map_comp, simplicialIntervalBoundary, coprod.inl_desc]
    exact ConcreteCategory.congr_hom h x
  have h₁ (x : E.obj T) : f (d.hom (e.inv (.inr x))) = E.map (intervalEndpoint C 1) x := by
    have h : (↾Sum.inr) ≫ e.inv ≫ d.hom ≫ f = E.map (intervalEndpoint C 1) := by
      rw [← Category.assoc _ e.inv, Types.binaryCoproductIso_inr_comp_inv,
        PreservesColimitPair.iso_hom,
        inr_coprodComparison_assoc, ← E.map_comp, simplicialIntervalBoundary, coprod.inr_desc]
    exact ConcreteCategory.congr_hom h x
  have hn (x y : E.obj T) : E.map (intervalEndpoint C 0) x ≠
      E.map (intervalEndpoint C 1) y := by
    intro h
    change ((SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ 0).app n) x =
      ((SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ 1).app n) y at h
    rw [SSet.stdSimplex.δ_zero_eq_const, SSet.stdSimplex.δ_one_eq_const] at h
    have h' := congrArg (fun t : (Δ[1] : SSet.{w}).obj n => t.down.toOrderHom 0) h
    exact (show (1 : Fin 2) ≠ 0 by decide) h'
  change Mono f
  let j := e.inv ≫ d.hom
  have hj : Mono (j ≫ f) := (CategoryTheory.mono_iff_injective _).2 (by
    intro a b h
    rcases a with x | x <;> rcases b with y | y
    · exact congrArg Sum.inl (Subsingleton.elim x y)
    · exact (hn x y ((h₀ x).symm.trans (h.trans (h₁ y)))).elim
    · exact (hn y x ((h₀ y).symm.trans (h.symm.trans (h₁ x)))).elim
    · exact congrArg Sum.inr (Subsingleton.elim x y))
  let : Mono (j ≫ f) := hj
  have hi : Function.Injective (j ≫ f) := CategoryTheory.injective_of_mono _
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y h
  have he : Function.Surjective j :=
    ((CategoryTheory.isIso_iff_bijective j).1 (inferInstanceAs (IsIso (e.inv ≫ d.hom)))).2
  obtain ⟨x', rfl⟩ := he x
  obtain ⟨y', rfl⟩ := he y
  exact congrArg j (hi h)

end CategoryTheory.PointedSimplicialPresheaf
