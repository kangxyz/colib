/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFieldSerreSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryMatching

/-!
# A generated choice of both original whole-source section pairs

The record retains actual native modules, sections, normalization equations and
whole-boundary zero ideals. Its existence theorem constructs every field from
finite-boundary trivialization and coherent Serre. It contains no correspondence
or homotopy assumptions and does not shrink the independent correction source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable (k K : Type u) [Field k] [CommRing K] (z : k[X] →+* K)
  {C Y A D : Scheme.{u}}
  (π : C ⟶ Spec (.of k)) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ Spec (.of k[X])) (hq : j ≫ π = p ≫ coordinateLineProjection k)
  (a : A ⟶ Spec (.of k[X]))
  (s : Spec (.of K) ⟶ Y) (hs : s ≫ p = coordinateMark k K z)
  (H : IsPullback s (𝟙 (Spec (.of K))) p (coordinateMark k K z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark k K z)))

local notation "XA" => pullback (j ≫ π) π
local notation "XN" => pullback (a ≫ coordinateLineProjection k) π
local notation "F" => divisorSheaf (compactificationGraph π j).ker
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (coordinateLineProjection k) π j p hq a
  (coordinateMark k K z) s hs d

/-- The actual global choices produced by Serre on the two distinct unchanged sources. -/
structure WholeFieldSectionData where
  T : XA.Modules
  T_invertible : IsInvertibleModule XA T
  N : XN.Modules
  N_invertible : IsInvertibleModule XN N
  aS : Γ(tensorModules F T, ⊤)
  bS : Γ(T, ⊤)
  nS : Γ(N, ⊤)
  dS : Γ(N, ⊤)
  normalized : (fixedFactorBoundaryIso iA F T
    (fullGraphDivisorFrame k K z π j p hq s hs H d hd)).hom.app ⊤
      (pullbackGlobalSections iA _ aS) = pullbackGlobalSections iA T bS
  scalar : pullbackGlobalSections iN N nS =
    correctionFullBoundaryCoordinate k K z π d a ha • pullbackGlobalSections iN N dS
  numerator_zero : letI := T_invertible
    zeroScheme _ ((Modules.pullback iA).obj (tensorModules F T))
      (pullbackGlobalSections iA _ aS) = ⊤
  denominator_zero : letI := T_invertible
    zeroScheme _ ((Modules.pullback iA).obj T) (pullbackGlobalSections iA T bS) = ⊤
  correctionNumerator_zero : letI := N_invertible
    zeroScheme _ ((Modules.pullback iN).obj N) (pullbackGlobalSections iN N nS) = ⊤
  correctionDenominator_zero : letI := N_invertible
    zeroScheme _ ((Modules.pullback iN).obj N) (pullbackGlobalSections iN N dS) = ⊤

/-- The section data is produced from the genuine compactification and full
mark, with no supplied frame, section, matching equation or presentation claim. -/
theorem nonempty_wholeFieldSectionData [IsAffine Y] [IsAffine A]
    [IsProper π] [IsOpenImmersion a] [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
    [IsFinite (d ≫ π)] [IsFinite (s ≫ j ≫ π)]
    (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L) :
    Nonempty (WholeFieldSectionData k K z π j p hq a s hs H d hd ha) := by
  obtain ⟨m, hm⟩ := exists_eventually_wholeField_normalized_sections
    k K z π j p hq s hs H d hd L hL
  obtain ⟨n, hn⟩ := exists_eventually_wholeField_scalar_sections
    k K z π j p hq s hs d hd L hL a ha
  obtain ⟨aS, bS, hA, haS, hbS⟩ := hm m le_rfl
  obtain ⟨nS, dS, hN, hnS, hdS⟩ := hn n le_rfl
  exact ⟨{
    T := tensorPowModule XA ((Modules.pullback (pullback.snd (j ≫ π) π)).obj L) (m : ℤ)
    T_invertible := inferInstance
    N := tensorPowModule XN
      ((Modules.pullback (pullback.snd (a ≫ coordinateLineProjection k) π)).obj L) (n : ℤ)
    N_invertible := inferInstance
    aS := aS
    bS := bS
    nS := nS
    dS := dS
    normalized := hA
    scalar := hN
    numerator_zero := haS
    denominator_zero := hbS
    correctionNumerator_zero := hnS
    correctionDenominator_zero := hdS }⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
