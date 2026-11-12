/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferenceBoundary

/-!
# Tests for the canonical trivialization away from section images
-/

open CategoryTheory AlgebraicGeometry

universe u

/-- The actual boundary avoids both section images; no Cartier or initial-frame input is needed. -/
example {X S B : Scheme.{u}} (q : X ⟶ S)
    [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S) (i : B ⟶ X)
    (his : Disjoint (Set.range i) (Set.range s))
    (hit : Disjoint (Set.range i) (Set.range t)) :
    Nonempty ((Scheme.Modules.pullback i).obj (Stacks.Divisors.differenceSheaf s.ker t.ker) ≅
      _root_.SheafOfModules.unit B.ringCatSheaf) :=
  ⟨Stacks.Divisors.sectionKernelDifferenceBoundaryIso q s t hs ht i his hit⟩

#print axioms Stacks.Divisors.sectionKernelDifferenceBoundaryIso
