/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialFunctionField

/-!
# Actual polynomial chart and endpoint Tor regression tests

The actual original boundary equality supplies nonvanishing. The native line
map and function-field maps remain in the conclusions. A chart fraction,
literal polynomial equality and both signed Tor values are produced together;
none is supplied as a comparison certificate.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open AlgebraicGeometry.PrincipalFamilyUnitOpen
open AlgebraicGeometry.PrincipalFamilyEndpointCuts

universe u

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, by trivial⟩⟩

local instance {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense ⟨j (genericPoint X), Set.mem_range_self _⟩⟩

local instance {k : Type u} [Field k] {C U : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) (u : U ⟶ C) [IsOpenImmersion u]
    [IsIntegral U] [IsIntegral (parameterSpace p)] :
    IsIntegral (parameterSpace (u ≫ p)) := by
  have : Nonempty (parameterSpace (u ≫ p)) := ⟨endpoint (u ≫ p) 0 (genericPoint U)⟩
  exact isIntegral_of_isOpenImmersion (lineMap p u)

-- The full original boundary may be nonreduced and need not itself be integral.
example {W B : Scheme.{u}} (b : B ⟶ W) [Nonempty B]
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) : f ≠ 0 :=
  section_ne_zero_of_boundary b f hf

-- No original curve or polynomial fraction identity is an input.
example {k : Type u} [Field k] {C W U B : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) (v : W ⟶ C) [IsOpenImmersion v]
    (u : U ⟶ C) [IsOpenImmersion u]
    [IsIntegral C] [IsIntegral W] [IsIntegral U] [IsIntegral (parameterSpace p)]
    [IsAffine U] [IsNoetherian U] [IsNoetherian (parameterSpace (u ≫ p))]
    (b : B ⟶ W) [Nonempty B] (f : Γ(W, ⊤)) (hf : b.appTop f = 1) :
    let := nonempty_ambientUnitOpen_of_boundary p v b f hf
    ∃ a d : Γ(U, ⊤),
      (lineMap p u).functionFieldMap (ambientRationalFunction p v f) =
        (parameterSpace (u ≫ p)).germToFunctionField ⊤ (numerator (u ≫ p) a d) /
          (parameterSpace (u ≫ p)).germToFunctionField ⊤ (denominator (u ≫ p) d) ∧
      ∀ (x : U) (_hx : coheight x = 1),
        weightedEndpointStalkTor (u ≫ p) 0 x (numerator (u ≫ p) a d) -
          weightedEndpointStalkTor (u ≫ p) 0 x (denominator (u ≫ p) d) = 0 ∧
        weightedEndpointStalkTor (u ≫ p) 1 x (numerator (u ≫ p) a d) -
          weightedEndpointStalkTor (u ≫ p) 1 x (denominator (u ≫ p) d) =
            U.ord (u.functionFieldMap (curveRationalFunction v f)) x := by
  let := nonempty_ambientUnitOpen_of_boundary p v b f hf
  obtain ⟨a, d, _, hpoly, hcuts⟩ := exists_chartFraction_endpointTor v p u f
    (section_ne_zero_of_boundary b f hf)
  exact ⟨a, d, hpoly, fun x hx => (hcuts x hx).2.2.2⟩

#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.section_ne_zero_of_boundary
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.exists_affineFraction
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.exists_affineFraction_endpointTor
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.curveRationalFunction_pullback
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.ambientRationalFunction_pullback
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.ambientRationalFunction_eq_linear
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.ambientRationalFunction_chart_fraction
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.exists_chartFraction_endpointTor
