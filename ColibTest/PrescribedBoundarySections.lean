/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.ProjectiveSpace.Sections.ClosedEmbedding

/-!
# Full-boundary prescribed-section producer tests

The boundary is an arbitrary closed subscheme, with no reducedness hypothesis. The test
retains arbitrary integer twists and produces the bound before choosing the boundary values.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Stacks.ProjectiveCohomology (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

example (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X Z : Scheme.{u}} (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    (i : Z ⟶ X) [IsClosedImmersion i] (M : X.Modules) [M.IsCoherent] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d →
      ∀ s : Γ((pullback i).obj ((pullbackTwistFunctor R n f d).obj M), ⊤),
      ∃ a : Γ((pullbackTwistFunctor R n f d).obj M, ⊤),
        pullbackGlobalSections i _ a = s :=
  exists_surjective_pullbackGlobalSections_pullbackTwist R n f i M

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) [Epi φ] : Epi ((pushforward f).map φ) :=
  epi_pushforward_map_of_isAffineHom f φ

#print axioms epi_pushforward_map_of_isAffineHom
#print axioms exists_surjective_twisted_boundary_pushforward_evaluation
#print axioms exists_surjective_pullbackGlobalSections_pullbackTwist
#print axioms exists_prescribed_boundary_section_pair
#print axioms exists_boundary_framed_section_pair
