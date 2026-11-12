/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.ProjectiveSpace.Sections.SerreLifting
import Colib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.BoundaryFrame

/-!
# Tests for prescribed quotient sections and boundary zero schemes

The quotient test uses two arbitrary coherent epimorphisms with one common bound. The
boundary test retains an arbitrary nonreduced boundary and checks literal ideal equality.
-/

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

example (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {F G H K : SheafOfModules.{u} (projRingSheaf (polyGrading R n))}
    [F.IsCoherent] [G.IsCoherent] [H.IsCoherent] [K.IsCoherent]
    (φ : G ⟶ F) (ψ : K ⟶ H) [Epi φ] [Epi ψ] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d →
      Function.Surjective
        ((SheafOfModules.evaluation (projRingSheaf (polyGrading R n)) (op ⊤)).map
          ((twistFunctor (polyGrading R n) d).map φ)).hom ∧
      Function.Surjective
        ((SheafOfModules.evaluation (projRingSheaf (polyGrading R n)) (op ⊤)).map
          ((twistFunctor (polyGrading R n) d).map ψ)).hom := by
  obtain ⟨B, hB⟩ := exists_surjective_twisted_evaluation_of_coherent_epi R n φ
  obtain ⟨C, hC⟩ := exists_surjective_twisted_evaluation_of_coherent_epi R n ψ
  exact ⟨max B C, fun d hd =>
    ⟨hB d ((le_max_left B C).trans hd), hC d ((le_max_right B C).trans hd)⟩⟩

example {X B : Scheme.{u}} (i : B ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : Hom.app e.hom ⊤ (pullbackGlobalSections i L s) = (1 : Γ(B, ⊤))) :
    (zeroScheme X L s).comap i = ⊤ :=
  zeroScheme_comap_eq_top_of_boundary_frame i L s e he

#print axioms AlgebraicGeometry.Scheme.Modules.exists_surjective_twisted_evaluation_of_coherent_epi
#print axioms AlgebraicGeometry.Scheme.Modules.isFinite_zeroScheme_of_boundary_frame
