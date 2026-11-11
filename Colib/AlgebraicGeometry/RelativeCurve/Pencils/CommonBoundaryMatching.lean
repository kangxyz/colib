/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.TwoSourceBoundaryMatching

/-!
# Geometric matching of the original two independent normalized section pairs

The whole polynomial Cartesian mark constructs the actual graph frame. The
independent correction source constructs its polynomial scalar unit. The given
source square forces their common-boundary scalar equality internally. Thus
only the two equations produced by Serre remain in the section-level interface;
no desired matching or pencil endpoint identity is a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable (R K : Type u) [CommRing R] [CommRing K] (z : R[X] →+* K)
  {C Y A B D : Scheme.{u}} (π : C ⟶ Spec (.of R)) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ Spec (.of R[X])) (hq : j ≫ π = p ≫ coordinateLineProjection R)
  (a : A ⟶ Spec (.of R[X])) (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (s : Spec (.of K) ⟶ Y) (hs : s ≫ p = coordinateMark R K z)
  (H : IsPullback s (𝟙 (Spec (.of K))) p (coordinateMark R K z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark R K z)))

local notation "F" => divisorSheaf (compactificationGraph π j).ker
local notation "σ" => divisorSheafGlobalSection (compactificationGraph π j).ker
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (coordinateLineProjection R) π j p hq a
  (coordinateMark R K z) s hs d
local notation "gA" => commonToLambda π j α
local notation "gN" => commonToPsi (coordinateLineProjection R) π j p hq a α β h
local notation "i" => commonBoundaryInclusion π j α s d

/-- The actual end and graph-times-poles start agree on the entire common
boundary. The numerator and denominator pairs live on their original distinct
products throughout the statement. -/
theorem relativeCommonBoundary_tensor
    (T : (pullback (j ≫ π) π).Modules)
    (N : (pullback (a ≫ coordinateLineProjection R) π).Modules)
    (aS : Γ(tensorModules F T, ⊤)) (bS : Γ(T, ⊤)) (nS dS : Γ(N, ⊤))
    (hA : (fixedFactorBoundaryIso iA F T
      (fullGraphDivisorFrame R K z π j p hq s hs H d hd)).hom.app ⊤
        (pullbackGlobalSections iA _ aS) = pullbackGlobalSections iA T bS)
    (hN : pullbackGlobalSections iN N nS =
      correctionFullBoundaryCoordinate R K z π d a ha • pullbackGlobalSections iN N dS) :
    pullbackGlobalSections i _
      (tensorSection ((Modules.pullback gA).obj (tensorModules F T))
        ((Modules.pullback gN).obj N) ⊤
          (pullbackGlobalSections gA _ aS) (pullbackGlobalSections gN N nS)) =
    pullbackGlobalSections i _
      (tensorSection ((Modules.pullback gA).obj (tensorModules F T))
        ((Modules.pullback gN).obj N) ⊤
          (pullbackGlobalSections gA _ (tensorSection F T ⊤ σ bS))
          (pullbackGlobalSections gN N dS)) := by
  apply boundary_tensor_matching_two_sources gA gN iA iN i
    (commonBoundaryToLambda π j α s d)
    (commonBoundaryToPsi (coordinateLineProjection R) π j p hq a α β h
      (coordinateMark R K z) s hs d)
    (commonBoundaryToLambda_inclusion π j α s d).symm
    (commonBoundaryToPsi_inclusion (coordinateLineProjection R) π j p hq a α β h
      (coordinateMark R K z) s hs d).symm F T N
    (fullGraphDivisorFrame R K z π j p hq s hs H d hd) σ aS bS nS dS _ hA hN
  exact commonBoundary_coordinate_eq R K z π j p hq a α β h s hs H d hd ha

end AlgebraicGeometry.Scheme.RelativeCurvePencil
