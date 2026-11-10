/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Simplex.NativeAction
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Composition
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The original additive simplex exterior endofunctor

Composition is specialized from the general native exterior composition theorem,
by directly specializing the established native exterior operation.
This adapts the original `Exterior/Simplex/Functor.lean` at a6805c4, retaining the
literal smooth product, actual signed cycles and existing incidence Tor pairing.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The actual simplex exterior preserves the existing signed incidence Tor composition. -/
theorem simplexExterior_comp (n : ℕ) {X Y Z : Cor k} (α : X ⟶ Y) (β : Y ⟶ Z) :
    simplexExterior n (α ≫ β) = simplexExterior n α ≫ simplexExterior n β := by
  simpa only [simplexExterior] using!
    Stacks.Chow.nativeExterior_incidenceTorPairing X.toSmoothSite Y.toSmoothSite Z.toSmoothSite
      (AlgebraicSimplex.smoothSiteObj k n) α β

/-- Adjoining the actual simplex acts functorially on signed finite correspondences. -/
def simplexExteriorFunctor (n : ℕ) : Cor k ⥤ Cor k where
  obj X := simplexProduct X n
  map α := simplexExterior n α
  map_id X := simplexExterior_id n X
  map_comp α β := simplexExterior_comp n α β

@[simp]
theorem simplexExteriorFunctor_obj (n : ℕ) (X : Cor k) :
    (simplexExteriorFunctor (k := k) n).obj X = simplexProduct X n := rfl

@[simp]
theorem simplexExteriorFunctor_map (n : ℕ) {X Y : Cor k} (α : X ⟶ Y) :
    (simplexExteriorFunctor (k := k) n).map α = simplexExterior n α := rfl

instance simplexExteriorFunctor_additive (n : ℕ) :
    (simplexExteriorFunctor (k := k) n).Additive where
  map_add := map_add (simplexExterior n) _ _

/-- The bundled additive endofunctor keeps the existing exterior map. -/
def simplexExteriorAdditiveFunctor (n : ℕ) : Cor k ⥤+ Cor k :=
  AdditiveFunctor.of (simplexExteriorFunctor (k := k) n)

end AlgebraicGeometry.Cor
