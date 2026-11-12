/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.OriginalPrincipalSupportCuts

/-! # Original principal-cycle support and full quotient regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)

example
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0) (s : Γ(X, ⊤))
    (hsm : X.presheaf.germ ⊤ x (by trivial) s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hsn : IsSMulRegular (X.presheaf.stalk x ⧸ Ideal.span {n})
      (X.presheaf.germ ⊤ x (by trivial) s))
    (hsd : IsSMulRegular (X.presheaf.stalk x ⧸ Ideal.span {d})
      (X.presheaf.germ ⊤ x (by trivial) s))
    (hfn : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {n})) ≠ ⊤)
    (hfd : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {d})) ≠ ⊤) :
    let F := algebraMap (X.presheaf.stalk x) X.functionField n /
      algebraMap (X.presheaf.stalk x) X.functionField d
    (∑ᶠ z ∈ principalSupportThrough X x F,
      (principalCycle X F) z * principalSupportCutLength X x z s) =
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
          Ideal.span {n}))).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
          Ideal.span {d}))).toNat : ℤ) :=
  principalCycle_supportCuts_eq_endpointDifference X x n d hn hd s hsm hsn hsd hfn hfd

#print axioms Stacks.Chow.mem_localPrincipalPrimes_union_of_ord_ne_zero

#print axioms Stacks.Chow.bijOn_fromSpecStalk_nonzeroPrincipalSupport

#print axioms Stacks.Chow.integralSupportCutLength_eq_principalSupportCutLength

#print axioms Stacks.Chow.principalCycle_supportCuts_eq_localPrimeSum

#print axioms Stacks.Chow.principalCycle_supportCuts_eq_endpointDifference

end Stacks.Chow
