/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.FiniteFiberFactorization
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Counting the simplices of a site fiber

The total space of sections of a simplicial presheaf bounds the simplices
of its original fiber once the sizes of the point's fibers are bounded.
The bound comes from representing each simplex by an actual germ.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C]

/-- Each simplex of the original fiber is the germ of a section of the
presheaf in that degree. -/
theorem exists_toPresheafFiber_app_eq (Φ : J.Point.{w}) (P : Cᵒᵖ ⥤ SSet.{w})
    (n : SimplexCategoryᵒᵖ) (s : (Φ.presheafFiber.obj P).obj n) :
    ∃ (U : C) (x : Φ.fiber.obj U) (a : (P.obj (op U)).obj n),
      (Φ.toPresheafFiber U x P).app n a = s := by
  let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type w)).obj n
  let e := (Φ.presheafFiberCompIso E).app P
  obtain ⟨U, x, a, ha⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := P ⋙ E) (e.inv s)
  have h := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app E U x P) a
  change e.hom (Φ.toPresheafFiber U x (P ⋙ E) a) =
    (Φ.toPresheafFiber U x P).app n a at h
  refine ⟨U, x, a, h.symm.trans ?_⟩
  rw [ha]
  exact ConcreteCategory.congr_hom e.inv_hom_id s

/-- A bound on all section simplices and on each indexing point fiber
gives the same regular cardinal bound on the actual stalk simplices. -/
theorem hasCardinalLT_presheafFiber_totalSimplices
    (Φ : J.Point.{w}) (P : Cᵒᵖ ⥤ SSet.{w}) (κ : Cardinal.{t}) [Fact κ.IsRegular]
    (hP : HasCardinalLT (Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, (P.obj q.1).obj q.2) κ)
    (hΦ : ∀ U : C, HasCardinalLT (Φ.fiber.obj U) κ) :
    HasCardinalLT (Σ n : SimplexCategoryᵒᵖ, (Φ.presheafFiber.obj P).obj n) κ := by
  let T := Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, (P.obj q.1).obj q.2
  let F : T → Type w := fun q => Φ.fiber.obj q.1.1.unop
  refine (hasCardinalLT_sigma F κ hP (fun q => hΦ q.1.1.unop)).of_surjective
    (fun ⟨q, x⟩ => ⟨q.1.2, (Φ.toPresheafFiber q.1.1.unop x P).app q.1.2 q.2⟩) ?_
  rintro ⟨n, s⟩
  obtain ⟨U, x, a, ha⟩ := Φ.exists_toPresheafFiber_app_eq P n s
  exact ⟨⟨⟨(op U, n), a⟩, x⟩, congrArg (Sigma.mk n) ha⟩

end CategoryTheory.GrothendieckTopology.Point
