/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferencePullback

/-!
# Tests for the actual pullback of section-divisor differences
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- All Cartier conditions are supplied by the smooth relative curve and actual sections.
-- The base change can in particular be the nonflat closed-fibre inclusion.
example {X S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S)
    [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst q g)).obj
        (Stacks.Divisors.differenceSheaf s.ker t.ker) ≅
      Stacks.Divisors.differenceSheaf (Scheme.baseChangedSection q g s hs).ker
        (Scheme.baseChangedSection q g t ht).ker) :=
  ⟨Stacks.Divisors.sectionKernelDifferencePullbackIso q g s t hs ht⟩

#print axioms Stacks.Divisors.sectionKernelDifferencePullbackIso
