/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.SectionKernelDifference

/-!
# Tests for the canonical Cartier-difference section and full local multiplicities
-/

open CategoryTheory AlgebraicGeometry Stacks.Divisors

universe u

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X]
  (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

local instance differenceInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (differenceSheaf D E) :=
  (isInvertible_differenceSheaf D E).toAlgebraicGeometry

example : IsRegularMeromorphicSection X.sheaf (differenceSheaf D E)
    (canonicalDifferenceMeromorphicSection D E) :=
  isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E

example [IsLocallyNoetherian X] (Z : AlgebraicGeometry.PrimeDivisor X) :
    (AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf D E)
      (canonicalDifferenceMeromorphicSection D E)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E)).val Z =
        ((Module.length (X.presheaf.stalk Z.genericPoint)
          ((X.presheaf.stalk Z.genericPoint) ⧸
            IdealSheafData.stalk D Z.genericPoint)).toNat : ℤ) -
        ((Module.length (X.presheaf.stalk Z.genericPoint)
          ((X.presheaf.stalk Z.genericPoint) ⧸
            IdealSheafData.stalk E Z.genericPoint)).toNat : ℤ) :=
  weilDivisorOfMeromorphicSection_canonicalDifference_apply D E Z

example [IsNoetherian X] :
    AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf D E)
      (canonicalDifferenceMeromorphicSection D E)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E) =
        effectiveCartierWeilDivisor D inferInstance -
          effectiveCartierWeilDivisor E inferInstance :=
  weilDivisorOfMeromorphicSection_canonicalDifference D E

example [IsNoetherian X] :
    AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf D D)
      (canonicalDifferenceMeromorphicSection D D)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D D) = 0 := by
  rw [weilDivisorOfMeromorphicSection_canonicalDifference, sub_self]

example [IsNoetherian X] :
    AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf E D)
      (canonicalDifferenceMeromorphicSection E D)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection E D) =
        -AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf D E)
          (canonicalDifferenceMeromorphicSection D E)
          (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E) := by
  rw [weilDivisorOfMeromorphicSection_canonicalDifference,
    weilDivisorOfMeromorphicSection_canonicalDifference, neg_sub]

example {S : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S) :
    IsRegularMeromorphicSection X.sheaf (differenceSheaf s.ker t.ker)
      (sectionKernelDifferenceMeromorphicSection q s t hs ht) :=
  isRegularMeromorphicSection_sectionKernelDifferenceMeromorphicSection q s t hs ht

#print axioms AlgebraicGeometry.orderOfVanishingMeromorphic_globalSection_eq_length
#print axioms Stacks.Divisors.weilDivisorOfMeromorphicSection_canonicalDifference
#print axioms Stacks.Divisors.sectionKernelDifferenceMeromorphicSection_divisor_apply
