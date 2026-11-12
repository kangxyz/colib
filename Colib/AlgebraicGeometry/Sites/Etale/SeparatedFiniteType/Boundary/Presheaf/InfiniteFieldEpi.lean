/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.Contraction.Epi
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Inputs

/-! # The constructed canonical boundary epimorphism family over infinite fields

The original-presheaf producer supplies the family from the two signed
corrections, the original overlap and the Jacobson open cover of the
whole zero fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

/-- Infinite fields admit the actual original canonical boundary epimorphisms. -/
theorem canonicalBoundaryEpi {k : Type u} [Field k] [Infinite k] :
    CanonicalBoundaryEpi k := by
  intro X P hP
  exact contractionToBoundary_epi X P hP

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
