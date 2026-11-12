/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferencePullback
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafBoundary

/-!
# The canonical boundary trivialization of a section-divisor difference

The boundary can be any scheme, including a nonreduced finite scheme. Avoiding
the actual section images supplies the trivialization; no initial frame is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- The canonical trivialization away from both section images, for a smooth relative curve. -/
def sectionKernelDifferenceBoundaryIso {X S B : Scheme.{u}} (q : X ⟶ S)
    [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S) (i : B ⟶ X)
    (his : Disjoint (Set.range i) (Set.range s))
    (hit : Disjoint (Set.range i) (Set.range t)) :
    (Scheme.Modules.pullback i).obj (differenceSheaf s.ker t.ker) ≅
      _root_.SheafOfModules.unit B.ringCatSheaf := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion (t ≫ q) := by rw [ht]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t q
  have := isEffectiveCartierDivisor_sectionKernel q s hs
  have := isEffectiveCartierDivisor_sectionKernel q t ht
  exact differenceSheafBoundaryIsoOfDisjointRange i s t his hit

end Stacks.Divisors
