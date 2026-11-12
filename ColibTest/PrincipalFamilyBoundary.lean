/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilySupport

/-! # Tests of whole-boundary polynomial normalization and genuine support finiteness -/

open AlgebraicGeometry CategoryTheory PrincipalFamilyUnitOpen

universe u

section
variable {R : Type u} [CommRing R] {W B : Scheme.{u}}
  (p : W ⟶ Spec (.of R)) (b : B ⟶ W) (f : Γ(W, ⊤))

-- No reducedness or closed-immersion assumption on the boundary is available.
example (hf : b.appTop f = 1) :
    (lineMap p b).appTop (familySection p f) = 1 :=
  boundary_familySection p b f hf

example : (endpoint p 0).appTop (familySection p f) = 1 := by simp
example : (endpoint p 1).appTop (familySection p f) = f := by simp

example (hf : b.appTop f = 1) (x : parameterSpace (b ≫ p)) :
    lineMap p b x ∈ unitOpen p f := boundary_mem_unitOpen p b f hf x
end

section
variable {R : Type u} [CommRing R] {C S V W B : Scheme.{u}}
  (p : S ⟶ Spec (.of R)) (q : C ⟶ S) [IsAffine S] [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
  [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]

example : (Set.range (lineMap (q ≫ p) j))ᶜ ⊆
    (ambientUnitOpen (q ≫ p) v f : Set (parameterSpace (q ≫ p))) :=
  complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf

example (x : parameterSpace (q ≫ p))
    (hx : letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
      Stacks.Chow.principalCycle (parameterSpace (q ≫ p))
        (ambientRationalFunction (q ≫ p) v f) x ≠ 0) :
    IsFinite ((Stacks.Chow.integralComponentAt x).subschemeι ≫ lineMap p q) :=
  principalFamily_support_isFinite p q j v b hcover f hf x hx
end

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.boundary_familySection
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.complement_subset_ambientUnitOpen
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.principalFamily_support_isFinite
