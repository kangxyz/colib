/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Neighborhood

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.SmoothSite

universe u

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : Scheme.SmoothSite S)
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X.left)

example : IsCofiltered (EtaleNeighborhood X ξ) := inferInstance

example : InitiallySmall.{u} (EtaleNeighborhood X ξ) := inferInstance

example (A B : EtaleNeighborhood X ξ) :
    ∃ (C : EtaleNeighborhood X ξ), Nonempty (C ⟶ A) ∧ Nonempty (C ⟶ B) :=
by
  obtain ⟨C, f, g, _⟩ := IsCofilteredOrEmpty.cone_objs A B
  exact ⟨C, ⟨f⟩, ⟨g⟩⟩

example (A : EtaleNeighborhood X ξ) :
    etaleNeighborhoodMark X ξ A ≫ (etaleNeighborhoodHom X ξ A).left = ξ :=
  etaleNeighborhoodMark_hom X ξ A

#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodToSmooth
#print axioms AlgebraicGeometry.Scheme.SmoothSite.exists_etaleNeighborhood_refinement
#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodInitiallySmall
