/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.OpenPrincipalSupportCuts

/-! # Regression for literal original support cuts under open restriction -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Chow

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example (x z : U) (s : Γ(X, ⊤)) :
    principalSupportCutLength U x z (j.appTop s) =
      principalSupportCutLength X (j x) (j z) s :=
  principalSupportCutLength_open j x z s

variable [IsIntegral U] [IsIntegral X] [IsLocallyNoetherian U] [IsLocallyNoetherian X]
    [IsDominant j]

example (x : U) (F : X.functionField) (s : Γ(X, ⊤)) :
    (∑ᶠ z ∈ principalSupportThrough U x (j.functionFieldMap F),
      (principalCycle U (j.functionFieldMap F)) z *
        principalSupportCutLength U x z (j.appTop s)) =
    ∑ᶠ z ∈ principalSupportThrough X (j x) F,
      (principalCycle X F) z * principalSupportCutLength X (j x) z s := by
  rw [← functionFieldEquiv_openImmersion_eq_schemeFunctionFieldMap j F]
  exact principalSupportCuts_open j x F s

#print axioms Stacks.Chow.integralComponentOpenMap_inclusion
#print axioms Stacks.Chow.sectionCut_length_open
#print axioms Stacks.Chow.principalSupportCutLength_open
#print axioms Stacks.Chow.bijOn_open_principalSupportThrough
#print axioms Stacks.Chow.principalSupportCuts_open
#print axioms Stacks.Chow.functionFieldEquiv_openImmersion_eq_schemeFunctionFieldMap
