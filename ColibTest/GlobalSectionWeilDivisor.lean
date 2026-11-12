/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.GlobalSectionWeilDivisor

/-! The actual zero scheme is Cartier by construction and has its full native Weil divisor. -/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

example {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    weilDivisorOfMeromorphicSection X L (meromorphicSectionOfGlobalSection L s)
        (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection L s hs) =
      effectiveCartierWeilDivisor (Stacks.Divisors.zeroScheme X L s)
        (isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs) :=
  weilDivisorOfMeromorphicSection_globalSection_eq_zeroScheme L s hs

#print axioms AlgebraicGeometry.genericPoint_mem_nonvanishingOpen_of_eval_top_ne_zero
#print axioms AlgebraicGeometry.weilDivisorOfMeromorphicSection_globalSection_eq_zeroScheme
