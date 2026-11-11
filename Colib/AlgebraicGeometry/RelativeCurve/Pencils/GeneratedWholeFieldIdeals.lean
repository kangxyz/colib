/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.GeneratedWholeFieldPencil

/-!
# Whole zero ideals of the genuinely generated pencil

The start and end are the literal product sections, with both source changes
retained. Native tensor-section zero ideals and canonical-section zero ideals
prove the product formulas, including nilpotents and coincident factors.
No cycle identity or desired support equality is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable (k K : Type u) [Field k] [CommRing K] (z : k[X] →+* K)
  {C Y A B D : Scheme.{u}}
  (π : C ⟶ Spec (.of k)) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ Spec (.of k[X])) (hq : j ≫ π = p ≫ coordinateLineProjection k)
  (a : A ⟶ Spec (.of k[X])) (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (s : Spec (.of K) ⟶ Y) (hs : s ≫ p = coordinateMark k K z)
  (H : IsPullback s (𝟙 (Spec (.of K))) p (coordinateMark k K z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark k K z)))

local notation "F" => divisorSheaf (compactificationGraph π j).ker
local notation "σ" => divisorSheafGlobalSection (compactificationGraph π j).ker
local notation "gA" => commonToLambda π j α
local notation "gN" => commonToPsi (coordinateLineProjection k) π j p hq a α β h
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (coordinateLineProjection k) π j p hq a
  (coordinateMark k K z) s hs d
local notation "i" => commonBoundaryInclusion π j α s d
local notation "qB" => commonProjection π j α

namespace WholeFieldSectionData

variable (c : WholeFieldSectionData k K z π j p hq a s hs H d hd ha)

/-- The actual product of numerators, on two different source products. -/
theorem commonEnd_zeroScheme : letI := c.T_invertible; letI := c.N_invertible
    zeroScheme _ (c.commonLine α β h) (c.commonEnd α β h) =
      (zeroScheme _ (tensorModules F c.T) c.aS).comap gA *
        (zeroScheme _ c.N c.nS).comap gN := by
  letI := c.T_invertible
  letI := c.N_invertible
  rw [commonEnd, commonLine, zeroScheme_tensorSection_eq_mul,
    zeroScheme_pullback, zeroScheme_pullback]

/-- The graph-times-poles start has its full original graph ideal, not merely
its reduced support or divisor class. -/
theorem commonStart_zeroScheme : letI := c.T_invertible; letI := c.N_invertible
    zeroScheme _ (c.commonLine α β h) (c.commonStart α β h) =
      ((compactificationGraph π j).ker.comap gA * (zeroScheme _ c.T c.bS).comap gA) *
        (zeroScheme _ c.N c.dS).comap gN := by
  letI := c.T_invertible
  letI := c.N_invertible
  rw [commonStart, commonLine, zeroScheme_tensorSection_eq_mul,
    ← zeroScheme_congr_iso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso gA F c.T),
    pullbackTensorIso_tensorSection, zeroScheme_tensorSection_eq_mul,
    zeroScheme_pullback, zeroScheme_canonicalSection, zeroScheme_pullback,
    zeroScheme_pullback]

/-- The actual denominator product retains both independent source changes. -/
theorem commonPole_zeroScheme : letI := c.T_invertible; letI := c.N_invertible
    zeroScheme _ (c.commonPoleLine α β h) (c.commonPole α β h) =
      (zeroScheme _ c.T c.bS).comap gA * (zeroScheme _ c.N c.dS).comap gN := by
  letI := c.T_invertible
  letI := c.N_invertible
  rw [commonPole, commonPoleLine, zeroScheme_tensorSection_eq_mul,
    zeroScheme_pullback, zeroScheme_pullback]

end WholeFieldSectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil
