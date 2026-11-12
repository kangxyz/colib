/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifference
public import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferencePullback

/-!
# The canonical meromorphic section of the original section-kernel difference

For a separated smooth relative curve the actual section kernels are Cartier.
On an integral locally Noetherian total space, their canonical difference section
has the signed full stalk quotient lengths of these original kernels. The base
is not assumed reduced; integrality is imposed explicitly on the total space.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X S : Scheme.{u}} (q : X ⟶ S)
  [IsSeparated q] [SmoothOfRelativeDimension 1 q] [IsIntegral X]
  (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S)

/-- A canonical regular meromorphic section on the literal difference of the two
original section kernels, before any base change or passage to a Picard representative. -/
def sectionKernelDifferenceMeromorphicSection :
    MeromorphicSection X.sheaf (differenceSheaf s.ker t.ker) := by
  letI := isEffectiveCartierDivisor_sectionKernel q s hs
  letI := isEffectiveCartierDivisor_sectionKernel q t ht
  exact canonicalDifferenceMeromorphicSection s.ker t.ker

/-- The geometric section-kernel construction supplies a regular meromorphic section. -/
theorem isRegularMeromorphicSection_sectionKernelDifferenceMeromorphicSection :
    IsRegularMeromorphicSection X.sheaf (differenceSheaf s.ker t.ker)
      (sectionKernelDifferenceMeromorphicSection q s t hs ht) := by
  have := isEffectiveCartierDivisor_sectionKernel q s hs
  have := isEffectiveCartierDivisor_sectionKernel q t ht
  exact isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection s.ker t.ker

/-- The actual section kernels determine each coefficient, with their full original
scheme structure and positive-minus-negative order. -/
@[colib_tag "COL-1050"]
theorem sectionKernelDifferenceMeromorphicSection_divisor_apply
    [IsLocallyNoetherian X] (Z : AlgebraicGeometry.PrimeDivisor X) :
    have := isEffectiveCartierDivisor_sectionKernel q s hs
    have := isEffectiveCartierDivisor_sectionKernel q t ht
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (differenceSheaf s.ker t.ker) :=
        (isInvertible_differenceSheaf s.ker t.ker).toAlgebraicGeometry
    (AlgebraicGeometry.weilDivisorOfMeromorphicSection X (differenceSheaf s.ker t.ker)
      (sectionKernelDifferenceMeromorphicSection q s t hs ht)
      (isRegularMeromorphicSection_sectionKernelDifferenceMeromorphicSection q s t hs ht)).val Z =
        effectiveCartierMultiplicity s.ker Z - effectiveCartierMultiplicity t.ker Z := by
  have := isEffectiveCartierDivisor_sectionKernel q s hs
  have := isEffectiveCartierDivisor_sectionKernel q t ht
  exact weilDivisorOfMeromorphicSection_canonicalDifference_apply s.ker t.ker Z

end Stacks.Divisors
