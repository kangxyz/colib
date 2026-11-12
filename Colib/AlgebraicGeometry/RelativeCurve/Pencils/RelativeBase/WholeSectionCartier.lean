/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.RetainedCartier
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GeneratedDivisors

/-!
# The original sections cut out Cartier divisors on their whole products

Their original zero schemes lie in the corresponding smooth retained opens.
The relative Cartier statement there gives the Cartier divisor on the whole
compact product, with its original closed scheme and all multiplicities.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable {S X C Y A Z D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S)
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range z))

namespace SectionData

variable [IsProper π] (c : SectionData q π j p hq a z s hs H e d hd ha)
  [IsAffine S] [IsAffine Y] [IsAffine A]
  {V : Scheme.{u}} [IsAffine V] (v : V ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))

local notation "b" => (j ≫ π)
local notation "Δ" => (Hom.ker (compactificationGraph π j))
local notation "L" => (tensorModules (divisorSheaf Δ) (SectionData.T c))
local notation "iA" => (fullGraphBoundaryMap π j s d)
local notation "iN" => (psiBoundaryInclusion q π j p hq a z s hs d)
local notation "vA" => (retainedProductInclusion b π v)
local notation "vN" => (retainedProductInclusion (a ≫ q) π v)

omit [IsAffine A] in
include hc in
/-- Both original first factors have their whole support in the same retained
product, and each is an effective Cartier divisor on its compact product. -/
theorem firstFactors_wholeCartier [IsLocallyNoetherian (pullback b π)] :
    letI := c.T_invertible
    let I := zeroScheme (pullback b π) L c.aS
    let J := zeroScheme (pullback b π) c.T c.bS
    (IsEffectiveCartierDivisor I ∧ Set.range I.subschemeι ⊆ Set.range vA) ∧
      (IsEffectiveCartierDivisor J ∧ Set.range J.subschemeι ⊆ Set.range vA) := by
  let := c.T_invertible
  let I := zeroScheme (pullback b π) L c.aS
  let J := zeroScheme (pullback b π) c.T c.bS
  have hcover := lambdaBoundary_retained_cover π j s d v hc
  have hI : Set.range I.subschemeι ⊆ Set.range vA :=
    whole_support_subset_of_boundary_comap_top vA iA I hcover
      ((zeroScheme_pullback iA L c.aS).symm.trans c.numerator_zero)
  have hJ : Set.range J.subschemeι ⊆ Set.range vA :=
    whole_support_subset_of_boundary_comap_top vA iA J hcover
      ((zeroScheme_pullback iA c.T c.bS).symm.trans c.denominator_zero)
  have hrel := c.retainedFirstFactors_finite_relativeCartier v hc
  exact ⟨⟨isEffectiveCartierDivisor_of_whole_support vA I hI
      (by simpa only [I, zeroScheme_pullback] using hrel.1.2.1), hI⟩,
    ⟨isEffectiveCartierDivisor_of_whole_support vA J hJ
      (by simpa only [J, zeroScheme_pullback] using hrel.2.2.1), hJ⟩⟩

omit [IsAffine Y] in
include hc in
/-- Both original correction factors have their whole support in the same
retained product and cut out Cartier divisors on the whole compact product. -/
theorem correctionFactors_wholeCartier [IsLocallyNoetherian (pullback (a ≫ q) π)] :
    letI := c.N_invertible
    let I := zeroScheme (pullback (a ≫ q) π) c.N c.nS
    let J := zeroScheme (pullback (a ≫ q) π) c.N c.dS
    (IsEffectiveCartierDivisor I ∧ Set.range I.subschemeι ⊆ Set.range vN) ∧
      (IsEffectiveCartierDivisor J ∧ Set.range J.subschemeι ⊆ Set.range vN) := by
  let := c.N_invertible
  let I := zeroScheme (pullback (a ≫ q) π) c.N c.nS
  let J := zeroScheme (pullback (a ≫ q) π) c.N c.dS
  have hcover := psiBoundary_retained_cover q π j p hq a z s hs d v hc
  have hI : Set.range I.subschemeι ⊆ Set.range vN :=
    whole_support_subset_of_boundary_comap_top vN iN I hcover
      ((zeroScheme_pullback iN c.N c.nS).symm.trans c.correctionNumerator_zero)
  have hJ : Set.range J.subschemeι ⊆ Set.range vN :=
    whole_support_subset_of_boundary_comap_top vN iN J hcover
      ((zeroScheme_pullback iN c.N c.dS).symm.trans c.correctionDenominator_zero)
  have hrel := c.retainedCorrectionFactors_finite_relativeCartier v hc
  exact ⟨⟨isEffectiveCartierDivisor_of_whole_support vN I hI
      (by simpa only [I, zeroScheme_pullback] using hrel.1.2.1), hI⟩,
    ⟨isEffectiveCartierDivisor_of_whole_support vN J hJ
      (by simpa only [J, zeroScheme_pullback] using hrel.2.2.1), hJ⟩⟩

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
