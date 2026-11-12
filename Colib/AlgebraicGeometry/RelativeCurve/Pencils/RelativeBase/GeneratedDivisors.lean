/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionData
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedBoundaryCover
/-! # Exact whole relative support data from the generated section pairs -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance (X : Scheme.{u}) (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

variable {S X C Y A Z D : Scheme.{u}}
  {q : X ⟶ S} [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  {π : C ⟶ S} [IsProper π]
  {j : Y ⟶ C} [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  {p : Y ⟶ X} {hq : j ≫ π = p ≫ q} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {hs : s ≫ p = z} {H : IsPullback s (𝟙 Z) p z}
  {e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf}
  {d : D ⟶ C} {hd : Disjoint (Set.range j) (Set.range d)}
  {ha : Disjoint (Set.range a) (Set.range z)}

local notation "XA" => pullback (j ≫ π) π
local notation "XN" => pullback (a ≫ q) π
local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion q π j p hq a z s hs d

namespace SectionData

variable (c : SectionData q π j p hq a z s hs H e d hd ha)
  [IsAffine S] [IsAffine Y] [IsAffine A] {V : Scheme.{u}} [IsAffine V]
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))

local notation "rA" => retainedProductInclusion (j ≫ π) π v
local notation "rN" => retainedProductInclusion (a ≫ q) π v

omit [IsAffine A] in
include hc in
/-- Both first-source factors have genuine whole finite-flat zero schemes. -/
theorem retainedFirstFactors_finite_relativeCartier :
    let hT := @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
    let ZA := @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rA).obj (tensorModules F c.T))
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA rA
        (tensorModules F c.T) hT) (pullbackGlobalSections rA _ c.aS)
    let ZB := @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rA).obj c.T)
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA rA
        c.T c.T_invertible) (pullbackGlobalSections rA _ c.bS)
    (IsFinite (ZA.subschemeι ≫ pullback.fst (j ≫ π) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (j ≫ π) (v ≫ π)) ZA) ∧
    (IsFinite (ZB.subschemeι ≫ pullback.fst (j ≫ π) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (j ≫ π) (v ≫ π)) ZB) := by
  let := c.T_invertible
  let : IsInvertibleModule XA (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
  let := retainedProduct_affine (j ≫ π) π v
  let := retainedProduct_smooth (j ≫ π) π v
  have hcover := lambdaBoundary_retained_cover π j s d v hc
  constructor
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iA (pullback.fst (j ≫ π) π) rA hcover
        (tensorModules F c.T) c.aS c.numerator_zero
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iA (pullback.fst (j ≫ π) π) rA hcover
        c.T c.bS c.denominator_zero

omit [IsAffine Y] in
include hc in
/-- Both correction factors are finite flat on the entire independent source A. -/
theorem retainedCorrectionFactors_finite_relativeCartier :
    let hN := @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN rN
      c.N c.N_invertible
    let ZN := @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rN).obj c.N) hN
      (pullbackGlobalSections rN _ c.nS)
    let ZD := @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rN).obj c.N) hN
      (pullbackGlobalSections rN _ c.dS)
    (IsFinite (ZN.subschemeι ≫ pullback.fst (a ≫ q) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (a ≫ q) (v ≫ π)) ZN) ∧
    (IsFinite (ZD.subschemeι ≫ pullback.fst (a ≫ q) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (a ≫ q) (v ≫ π)) ZD) := by
  let := c.N_invertible
  let := retainedProduct_affine (a ≫ q) π v
  let := retainedProduct_smooth (a ≫ q) π v
  have hcover := psiBoundary_retained_cover (q) π j p hq a
    (z) s hs d v hc
  constructor
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iN
        (pullback.fst (a ≫ q) π) rN hcover c.N c.nS
        c.correctionNumerator_zero
  · simpa only [retainedProductInclusion_fst] using
      finite_relativeCartier_of_boundary_zero iN
        (pullback.fst (a ≫ q) π) rN hcover c.N c.dS
        c.correctionDenominator_zero

private theorem finiteRelativeCartier_of_ideal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I J : X.IdealSheafData} (h : I = J)
    (hI : IsFinite (I.subschemeι ≫ f) ∧ IsRelativeEffectiveCartierDivisor f I) :
    IsFinite (J.subschemeι ≫ f) ∧ IsRelativeEffectiveCartierDivisor f J :=
  h ▸ hI

omit [IsAffine A] in
include hc in
/-- The original numerator and pole supports pulled to the retained open. -/
theorem retainedFirstFactors_comap_finite_relativeCartier :
    let hT := @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
    let IA := (@AlgebraicGeometry.zeroScheme XA (tensorModules F c.T) hT c.aS).comap rA
    let IB := (@AlgebraicGeometry.zeroScheme XA c.T c.T_invertible c.bS).comap rA
    (IsFinite (IA.subschemeι ≫ pullback.fst (j ≫ π) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (j ≫ π) (v ≫ π)) IA) ∧
    (IsFinite (IB.subschemeι ≫ pullback.fst (j ≫ π) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (j ≫ π) (v ≫ π)) IB) := by
  let : IsInvertibleModule XA c.T := c.T_invertible
  let : IsInvertibleModule XA (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
  have hAB := c.retainedFirstFactors_finite_relativeCartier v hc
  exact ⟨finiteRelativeCartier_of_ideal_eq (pullback.fst (j ≫ π) (v ≫ π))
      (zeroScheme_pullback rA (tensorModules F c.T) c.aS) hAB.1,
    finiteRelativeCartier_of_ideal_eq (pullback.fst (j ≫ π) (v ≫ π))
      (zeroScheme_pullback rA c.T c.bS) hAB.2⟩

omit [IsAffine Y] in
include hc in
/-- Both original correction supports pulled to the retained open. -/
theorem retainedCorrectionFactors_comap_finite_relativeCartier :
    let IN := (@AlgebraicGeometry.zeroScheme XN c.N c.N_invertible c.nS).comap rN
    let ID := (@AlgebraicGeometry.zeroScheme XN c.N c.N_invertible c.dS).comap rN
    (IsFinite (IN.subschemeι ≫ pullback.fst (a ≫ q) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (a ≫ q) (v ≫ π)) IN) ∧
    (IsFinite (ID.subschemeι ≫ pullback.fst (a ≫ q) (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst (a ≫ q) (v ≫ π)) ID) := by
  let : IsInvertibleModule XN c.N := c.N_invertible
  have hND := c.retainedCorrectionFactors_finite_relativeCartier v hc
  exact ⟨finiteRelativeCartier_of_ideal_eq (pullback.fst (a ≫ q) (v ≫ π))
      (zeroScheme_pullback rN c.N c.nS) hND.1,
    finiteRelativeCartier_of_ideal_eq (pullback.fst (a ≫ q) (v ≫ π))
      (zeroScheme_pullback rN c.N c.dS) hND.2⟩

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
