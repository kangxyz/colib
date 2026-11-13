/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.FiniteFiberFactorization
public import Colib.CategoryTheory.Sites.Simplicial.Subpresheaf
public import Colib.CategoryTheory.Subfunctor.BoundedGeneration
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Bounded simplicial subpresheaves supporting finite maps into a site fiber

A finite simplicial map into the original site fiber factors through a
bounded subpresheaf. Use one neighborhood representative and generate
the subpresheaf from its actual simplices. This is the support step of
Jardine, *Simplicial presheaves*, Lemma 2.4, pp. 65–66.
https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
universe t w v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C]
  {P : Cᵒᵖ ⥤ SSet.{w}}

/-- A regular cardinal bound on the total space of original section simplices. -/
abbrev HasBoundedSections (A : Subpresheaf P) (κ : Cardinal.{t}) : Prop :=
  HasCardinalLT (Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, A.obj q) κ

/-- A contained simplicial subpresheaf has the same bound on section simplices. -/
theorem hasBoundedSections_of_le {A B : Subpresheaf P} {κ : Cardinal.{t}}
    (h : A ≤ B) (hB : HasBoundedSections B κ) : HasBoundedSections A κ := by
  let code (s : Σ q, A.obj q) : Σ q, B.obj q := ⟨s.1, ⟨s.2.val, h s.1 s.2.property⟩⟩
  refine hB.of_injective code ?_
  rintro ⟨U, s⟩ ⟨V, t⟩ e
  have eq := congrArg Sigma.fst e
  change U = V at eq
  subst V
  apply congrArg (Sigma.mk U)
  apply Subtype.ext
  have eh := (Sigma.mk.inj_iff.1 e).2
  have es : (⟨s.val, h U s.property⟩ : B.obj U) = ⟨t.val, h U t.property⟩ := eq_of_heq eh
  exact congrArg (fun z : B.obj U => z.val) es

/-- A finite simplicial set has fewer simplices than any uncountable cardinal. -/
theorem hasCardinalLT_totalSimplices_of_finite (K : SSet.{w}) [K.Finite]
    (κ : Cardinal.{t}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ) :
    HasCardinalLT (Σ n : SimplexCategoryᵒᵖ, K.obj n) κ := by
  have hn : HasCardinalLT ℕ κ := by
    simpa only [HasCardinalLT, Cardinal.mk_nat, Cardinal.lift_aleph0,
      Cardinal.lift_id'.{0, t}] using hκ
  have h := hasCardinalLT_sigma (fun n : ℕ => K.obj (op (SimplexCategory.mk n))) κ hn
    (fun _ => hasCardinalLT_of_finite _ _ hκ.le)
  refine h.of_surjective (fun ⟨n, x⟩ => ⟨op (SimplexCategory.mk n), x⟩) ?_
  rintro ⟨⟨⟨n⟩⟩, x⟩
  exact ⟨⟨n, x⟩, rfl⟩

/-- A finite map into the original fiber comes from a bounded simplicial
subpresheaf when the original restriction arrows have the same bound. -/
theorem exists_boundedSubpresheaf_factorization_of_finite
    [LocallySmall.{w} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
    {K : SSet.{w}} [K.Finite] (f : K ⟶ Φ.presheafFiber.obj P)
    (κ : Cardinal.{t}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ) :
    ∃ A : Subpresheaf P, HasBoundedSections A κ ∧
      ∃ g : K ⟶ Φ.presheafFiber.obj (toPresheaf A), g ≫ Φ.presheafFiber.map (inclusion A) = f := by
  obtain ⟨U, x, g, hg⟩ := Φ.exists_toPresheafFiber_factorization_of_finite P f
  let A := generatedByMap g
  have hA : HasBoundedSections A κ :=
    Subfunctor.hasCardinalLT_totalSections_generated (F := Functor.uncurry.obj P)
      (U := fun s : Σ n : SimplexCategoryᵒᵖ, K.obj n => (op U, s.1))
      (fun s => g.app s.1 s.2) κ
      (hasCardinalLT_totalSimplices_of_finite K κ hκ) (fun s => hC (op U, s.1))
  refine ⟨A, hA, factorThroughGeneratedByMap g ≫ Φ.toPresheafFiber U x (toPresheaf A), ?_⟩
  rw [Category.assoc, Φ.toPresheafFiber_naturality, ← Category.assoc,
    factorThroughGeneratedByMap_inclusion, hg]

end CategoryTheory.SimplicialSubpresheaf
