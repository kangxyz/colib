/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.GeneratedWholeFieldSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedBoundaryCover
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedFamilyRestriction

/-!
# The genuine whole finite-flat polynomial pencil from the generated sections

Both source pairs are the actual Serre choices. Their whole-boundary matching
and nonvanishing are proved, producing a frame from the actual start section.
Properness and the retained smooth affine curve then give finite flatness of
the complete polynomial family. Neither a family frame nor finite flatness of
the family is an extra input. The pole is treated by the same whole support
argument. All parameter values and nilpotents are retained.
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

/-- The literal common numerator line, retaining its original pullback bracketing. -/
def commonLine : (commonAmbient π j α).Modules :=
  tensorModules ((Modules.pullback gA).obj (tensorModules F c.T)) ((Modules.pullback gN).obj c.N)

/-- The literal graph-times-poles start; no expected zero ideal is substituted. -/
def commonStart : Γ(c.commonLine α β h, ⊤) :=
  tensorSection _ _ ⊤
    (pullbackGlobalSections gA _ (tensorSection F c.T ⊤ σ c.bS))
    (pullbackGlobalSections gN c.N c.dS)

/-- The literal product of the two independently generated numerators. -/
def commonEnd : Γ(c.commonLine α β h, ⊤) :=
  tensorSection _ _ ⊤ (pullbackGlobalSections gA _ c.aS) (pullbackGlobalSections gN c.N c.nS)

/-- The actual common pole line. -/
def commonPoleLine : (commonAmbient π j α).Modules :=
  tensorModules ((Modules.pullback gA).obj c.T) ((Modules.pullback gN).obj c.N)

/-- The actual product of the original denominator sections. -/
def commonPole : Γ(c.commonPoleLine α β h, ⊤) :=
  tensorSection _ _ ⊤ (pullbackGlobalSections gA c.T c.bS) (pullbackGlobalSections gN c.N c.dS)

/-- The normalization equations, and not any homotopy hypothesis, imply whole-boundary matching. -/
theorem commonEnd_boundary_eq_start :
    pullbackGlobalSections i _ (c.commonEnd α β h) =
      pullbackGlobalSections i _ (c.commonStart α β h) :=
  relativeCommonBoundary_tensor k K z π j p hq a α β h s hs H d hd ha
    c.T c.N c.aS c.bS c.nS c.dS c.normalized c.scalar

/-- The actual numerator endpoint has no zeros anywhere on the common boundary. -/
theorem commonEnd_boundary_zero : letI := c.T_invertible; letI := c.N_invertible
    zeroScheme _ ((Modules.pullback i).obj (c.commonLine α β h))
      (pullbackGlobalSections i _ (c.commonEnd α β h)) = ⊤ := by
  letI := c.T_invertible
  letI := c.N_invertible
  apply zeroScheme_boundary_tensorSection_eq_top
  · exact zeroScheme_boundary_after_sourceChange gA iA i
      (commonBoundaryToLambda π j α s d) (commonBoundaryToLambda_inclusion π j α s d).symm
      _ c.aS c.numerator_zero
  · exact zeroScheme_boundary_after_sourceChange gN iN i
      (commonBoundaryToPsi (coordinateLineProjection k) π j p hq a α β h
        (coordinateMark k K z) s hs d)
      (commonBoundaryToPsi_inclusion (coordinateLineProjection k) π j p hq a α β h
        (coordinateMark k K z) s hs d).symm _ c.nS c.correctionNumerator_zero

/-- The start is nonvanishing on the whole boundary as a consequence of actual matching. -/
theorem commonStart_boundary_zero : letI := c.T_invertible; letI := c.N_invertible
    zeroScheme _ ((Modules.pullback i).obj (c.commonLine α β h))
      (pullbackGlobalSections i _ (c.commonStart α β h)) = ⊤ := by
  rw [← c.commonEnd_boundary_eq_start α β h]
  exact c.commonEnd_boundary_zero α β h

/-- The denominator product also has no zeros on the entire common boundary. -/
theorem commonPole_boundary_zero : letI := c.T_invertible; letI := c.N_invertible
    zeroScheme _ ((Modules.pullback i).obj (c.commonPoleLine α β h))
      (pullbackGlobalSections i _ (c.commonPole α β h)) = ⊤ := by
  letI := c.T_invertible
  letI := c.N_invertible
  apply zeroScheme_boundary_tensorSection_eq_top
  · exact zeroScheme_boundary_after_sourceChange gA iA i
      (commonBoundaryToLambda π j α s d) (commonBoundaryToLambda_inclusion π j α s d).symm
      _ c.bS c.denominator_zero
  · exact zeroScheme_boundary_after_sourceChange gN iN i
      (commonBoundaryToPsi (coordinateLineProjection k) π j p hq a α β h
        (coordinateMark k K z) s hs d)
      (commonBoundaryToPsi_inclusion (coordinateLineProjection k) π j p hq a α β h
        (coordinateMark k K z) s hs d).symm _ c.dS c.correctionDenominator_zero

variable [IsProper π] [IsAffine B] {V : Scheme.{u}} [IsAffine V]
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))

local notation "r" => retainedProductInclusion qB π v

/-- The full actual polynomial family is finite flat, with its literal retained
source map. Its boundary frame was constructed from the generated sections. -/
theorem retainedFamily_finite_flat : letI := c.T_invertible; letI := c.N_invertible
    IsFinite (PolynomialSectionPencil.familySource qB (pullback.fst qB (v ≫ π))
      ((Modules.pullback r).obj (c.commonLine α β h))
      (pullbackGlobalSections r _ (c.commonStart α β h))
      (pullbackGlobalSections r _ (c.commonEnd α β h))) ∧
    Flat (PolynomialSectionPencil.familySource qB (pullback.fst qB (v ≫ π))
      ((Modules.pullback r).obj (c.commonLine α β h))
      (pullbackGlobalSections r _ (c.commonStart α β h))
      (pullbackGlobalSections r _ (c.commonEnd α β h))) := by
  letI := c.T_invertible
  letI := c.N_invertible
  letI := retainedProduct_affine qB π v
  letI := retainedProduct_smooth qB π v
  let e := frameOfZeroSchemeTop _ (pullbackGlobalSections i _ (c.commonStart α β h))
    (c.commonStart_boundary_zero α β h)
  have hf := PolynomialSectionPencil.finite_flat_retainedFamily_of_boundary_frame r qB
    (pullback.fst qB π) i (c.commonLine α β h) (c.commonStart α β h) (c.commonEnd α β h)
    (commonBoundary_retained_cover π v j α s d hc)
    (c.commonEnd_boundary_eq_start α β h).symm e.hom
    (frameOfZeroSchemeTop_section _ _ _)
  simpa only [retainedProductInclusion_fst] using hf

/-- The constant pole's entire zero scheme is likewise finite and relative
Cartier; its constant polynomial family then follows by ConstantFamily. -/
theorem retainedPole_finite_relativeCartier : letI := c.T_invertible; letI := c.N_invertible
    IsFinite ((zeroScheme _ ((Modules.pullback r).obj (c.commonPoleLine α β h))
      (pullbackGlobalSections r _ (c.commonPole α β h))).subschemeι ≫
        pullback.fst qB (v ≫ π)) ∧
    IsRelativeEffectiveCartierDivisor (pullback.fst qB (v ≫ π))
      (zeroScheme _ ((Modules.pullback r).obj (c.commonPoleLine α β h))
        (pullbackGlobalSections r _ (c.commonPole α β h))) := by
  letI := c.T_invertible
  letI := c.N_invertible
  letI := retainedProduct_affine qB π v
  letI := retainedProduct_smooth qB π v
  have hp := finite_relativeCartier_of_boundary_zero i (pullback.fst qB π) r
    (commonBoundary_retained_cover π v j α s d hc)
    (c.commonPoleLine α β h) (c.commonPole α β h) (c.commonPole_boundary_zero α β h)
  simpa only [retainedProductInclusion_fst] using hp

end WholeFieldSectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil
