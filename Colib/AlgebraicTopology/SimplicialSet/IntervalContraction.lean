/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The last-vertex contraction of the simplicial interval

The coordinatewise maximum on the standard simplicial interval starts at
the identity and ends at the constant map to the last vertex. Its restriction
to the last vertex of the first factor is constant throughout the interval.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

namespace SSet

/-- The pointwise maximum of two monotone maps to the simplicial interval. -/
def intervalMax : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[1] where
  app _ := ↾fun z => stdSimplex.objMk
    ⟨fun i => max (stdSimplex.asOrderHom z.1 i) (stdSimplex.asOrderHom z.2 i),
      fun _ _ hij => max_le_max
        ((stdSimplex.asOrderHom z.1).monotone hij)
        ((stdSimplex.asOrderHom z.2).monotone hij)⟩
  naturality _ _ _ := by rfl

@[simp]
theorem intervalMax_app_asOrderHom {n : SimplexCategoryᵒᵖ}
    (z : (Δ[1] ⊗ Δ[1] : SSet.{u}).obj n) (i : Fin (n.unop.len + 1)) :
    stdSimplex.asOrderHom (intervalMax.app n z) i =
      max (stdSimplex.asOrderHom z.1 i) (stdSimplex.asOrderHom z.2 i) :=
  rfl

/-- At time zero the maximum is the identity on the interval factor. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_δ_one_comp_intervalMax :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 2)) ≫ intervalMax =
      fst (Δ[1] : SSet.{u}) Δ[0] := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change max (stdSimplex.asOrderHom z.1 i)
    (stdSimplex.asOrderHom ((stdSimplex.δ (1 : Fin 2)).app n z.2) i) =
      stdSimplex.asOrderHom z.1 i
  rw [stdSimplex.δ_one_eq_const]
  exact max_eq_left (Fin.zero_le _)

/-- At time one the maximum is the constant map to the last vertex. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_δ_zero_comp_intervalMax :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2)) ≫ intervalMax =
      snd (Δ[1] : SSet.{u}) Δ[0] ≫ stdSimplex.δ (0 : Fin 2) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change max (stdSimplex.asOrderHom z.1 i)
    (stdSimplex.asOrderHom ((stdSimplex.δ (0 : Fin 2)).app n z.2) i) =
      stdSimplex.asOrderHom ((stdSimplex.δ (0 : Fin 2)).app n z.2) i
  rw [stdSimplex.δ_zero_eq_const]
  change max (stdSimplex.asOrderHom z.1 i) (1 : Fin 2) = 1
  exact max_eq_right (Fin.le_last _)

/-- The last vertex in the interval factor stays fixed at every time. -/
@[reassoc (attr := simp)]
theorem δ_zero_whiskerRight_comp_intervalMax :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ intervalMax =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ stdSimplex.δ (0 : Fin 2) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change max (stdSimplex.asOrderHom ((stdSimplex.δ (0 : Fin 2)).app n z.1) i)
    (stdSimplex.asOrderHom z.2 i) =
      stdSimplex.asOrderHom ((stdSimplex.δ (0 : Fin 2)).app n z.1) i
  rw [stdSimplex.δ_zero_eq_const]
  change max (1 : Fin 2) (stdSimplex.asOrderHom z.2 i) = 1
  exact max_eq_left (Fin.le_last _)

end SSet

attribute [colib_tag "COL-0385"]
  SSet.intervalMax
  SSet.whiskerLeft_δ_one_comp_intervalMax
  SSet.whiskerLeft_δ_zero_comp_intervalMax
  SSet.δ_zero_whiskerRight_comp_intervalMax
