/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.GeneratedWholeFieldPencil

/-!
# The four genuine whole finite-flat factor divisors

The four Serre sections have empty zero schemes on the full boundary. Properness
and the actual retained smooth affine curve therefore produce finiteness and
relative Cartier structure for each whole zero scheme, on its unchanged source.
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
  [IsProper π] [IsAffine Y] [IsAffine A] {V : Scheme.{u}} [IsAffine V]
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))

local notation "rA" => retainedProductInclusion (j ≫ π) π v
local notation "rN" => retainedProductInclusion (a ≫ coordinateLineProjection k) π v

/-- Both first-source factors have genuine whole finite-flat zero schemes. -/
theorem retainedFirstFactors_finite_relativeCartier :
    letI := c.T_invertible
    let ZA := zeroScheme _ ((Modules.pullback rA).obj (tensorModules F c.T))
      (pullbackGlobalSections rA _ c.aS)
    let ZB := zeroScheme _ ((Modules.pullback rA).obj c.T) (pullbackGlobalSections rA _ c.bS)
    (IsFinite (ZA.subschemeι ≫ pullback.fst (j ≫ π) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (j ≫ π) (v ≫ π)) ZA) ∧
    (IsFinite (ZB.subschemeι ≫ pullback.fst (j ≫ π) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (j ≫ π) (v ≫ π)) ZB) := by
  letI := c.T_invertible
  letI := retainedProduct_affine (j ≫ π) π v
  letI := retainedProduct_smooth (j ≫ π) π v
  have hcover := lambdaBoundary_retained_cover π j s d v hc
  constructor
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iA (pullback.fst (j ≫ π) π) rA hcover
        (tensorModules F c.T) c.aS c.numerator_zero
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iA (pullback.fst (j ≫ π) π) rA hcover
        c.T c.bS c.denominator_zero

/-- Both correction factors are finite flat on the entire independent source A. -/
theorem retainedCorrectionFactors_finite_relativeCartier :
    letI := c.N_invertible
    let ZN := zeroScheme _ ((Modules.pullback rN).obj c.N) (pullbackGlobalSections rN _ c.nS)
    let ZD := zeroScheme _ ((Modules.pullback rN).obj c.N) (pullbackGlobalSections rN _ c.dS)
    (IsFinite (ZN.subschemeι ≫ pullback.fst (a ≫ coordinateLineProjection k) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (a ≫ coordinateLineProjection k) (v ≫ π)) ZN) ∧
    (IsFinite (ZD.subschemeι ≫ pullback.fst (a ≫ coordinateLineProjection k) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (a ≫ coordinateLineProjection k) (v ≫ π)) ZD) := by
  letI := c.N_invertible
  letI := retainedProduct_affine (a ≫ coordinateLineProjection k) π v
  letI := retainedProduct_smooth (a ≫ coordinateLineProjection k) π v
  have hcover := psiBoundary_retained_cover (coordinateLineProjection k) π j p hq a
    (coordinateMark k K z) s hs d v hc
  constructor
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iN
        (pullback.fst (a ≫ coordinateLineProjection k) π) rN hcover c.N c.nS
        c.correctionNumerator_zero
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iN
        (pullback.fst (a ≫ coordinateLineProjection k) π) rN hcover c.N c.dS
        c.correctionDenominator_zero

end WholeFieldSectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil
