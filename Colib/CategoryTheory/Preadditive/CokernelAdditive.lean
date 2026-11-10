/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/CategoryTheory/CokernelAdditive.lean`, blob
`a4a7634a88ea3d7fec315d73fc435081ec63815f`.

# Additivity of ordinary functor-category cokernels

An objectwise epimorphic natural transformation out of an additive functor
forces its target to be additive. In particular an ordinary functor-category
cokernel with additive target can be bundled as an additive functor. This
requires no abelian-category structure on the category of additive functors.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- Additivity descends along an objectwise epimorphic natural transformation. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/CokernelAdditive.lean:32-37"
  "adaptation" "Additivity descends through actual objectwise epimorphisms"]
theorem additive_of_epi_app {F G : C ⥤ D} [F.Additive] (η : F ⟶ G)
    [∀ X, Epi (η.app X)] : G.Additive where
  map_add {X Y f g} := by
    apply (cancel_epi (η.app X)).mp
    rw [← η.naturality, F.map_add, Preadditive.add_comp,
      Preadditive.comp_add, η.naturality, η.naturality]

/-- An ordinary functor-category cokernel of a map into an additive functor
is additive in source arrows. -/
theorem cokernel_additive [HasPushouts D] {F G : C ⥤ D}
    [G.Additive] (η : F ⟶ G) [HasCokernel η] : (cokernel η).Additive :=
  additive_of_epi_app (cokernel.π η)

end CategoryTheory.Functor
