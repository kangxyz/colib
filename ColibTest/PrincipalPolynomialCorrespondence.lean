/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialFamily

/-! # Tests of codimension-one dominance and the constructed native principal correspondence -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PrincipalFamilyUnitOpen

universe u

section
variable {D V S : Scheme.{u}} (i : D ⟶ V) [IsClosedImmersion i]
  (q : V ⟶ S) [SmoothOfRelativeDimension 1 q] [IsSeparated q]
  [IsFinite (i ≫ q)]

-- The actual finite support is not assumed flat, reduced or integral.
example (x : D) (hx : Order.coheight (i x) = 1) : q (i x) ∈ genericPoints S :=
  Scheme.image_mem_genericPoints_of_coheight_one_finite_closed_support i q x hx
end

section
variable {R : Type u} [CommRing R] {C X Y V W B : Scheme.{u}}
  (p : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
  [IsAffine X] [IsSeparated t] [LocallyOfFiniteType t]
  (q : C ⟶ X) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
  [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]
  (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ t)

-- No extra finite-support, dominance, flatness, or endpoint-cycle certificate.
-- No reducedness is imposed on B; hf is equality on the full boundary scheme.
example : Stacks.Chow.finiteCorrespondences (projection p ≫ p) t :=
  Stacks.Chow.PrincipalPolynomialFamily.correspondence p t q j v b hcover f hf g hg

example :
    (Stacks.Chow.PrincipalPolynomialFamily.correspondence p t q j v b hcover f hf g hg).val ∈
      Stacks.Chow.finiteCorrespondences (projection p ≫ p) t :=
  (Stacks.Chow.PrincipalPolynomialFamily.correspondence p t q j v b hcover f hf g hg).property
end

#print axioms AlgebraicGeometry.Scheme.image_mem_genericPoints_of_coheight_one_finite_closed_support
#print axioms Stacks.Chow.principalCycle_support_dominates_component
#print axioms Stacks.Chow.PrincipalBoundary.componentCorrespondence_val
#print axioms Stacks.Chow.PrincipalPolynomialFamily.correspondence
