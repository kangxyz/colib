/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FieldCoefficientFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeBoundaryClosed
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FullBoundaryCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedBoundarySections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.ScalarBoundarySections
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic

/-!
# The two genuine Serre pairs on their unchanged original field sources

The ample coefficient is pulled from the proper compactification by an affine
projection. All coefficient-power boundary frames are produced from the finite
boundary over the field. The graph frame and scalar unit are also produced by
the full polynomial marking and original disjointness. Serre then constructs
the actual global pairs. Neither source is shrunk, and no desired section or
frame is an additional input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Ample Stacks.Divisors
open Stacks.AlgebraicGeometry.RelativeSerreVanishing

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens
  compactificationGraphIdeal_isEffectiveCartierDivisor

variable (k K : Type u) [Field k] [CommRing K] (z : k[X] →+* K)
  {C Y A D : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (π : C ⟶ Spec (.of k)) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ Spec (.of k[X])) (hq : j ≫ π = p ≫ coordinateLineProjection k)
  (s : Spec (.of K) ⟶ Y) (hs : s ≫ p = coordinateMark k K z)
  (H : IsPullback s (𝟙 (Spec (.of K))) p (coordinateMark k K z))
  (d : D ⟶ C) [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  [IsFinite (d ≫ π)] [IsFinite (s ≫ j ≫ π)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L)

local notation "XA" => pullback (j ≫ π) π
local notation "LA" => (Modules.pullback (pullback.snd (j ≫ π) π)).obj L
local notation "F" => divisorSheaf (compactificationGraph π j).ker
local notation "iA" => fullGraphBoundaryMap π j s d

/-- Produce the actual first pair for every sufficiently large coefficient
power on the unchanged original lambda product. -/
theorem exists_eventually_wholeField_normalized_sections :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ aS : Γ(tensorModules F (tensorPowModule XA LA (n : ℤ)), ⊤),
      ∃ bS : Γ(tensorPowModule XA LA (n : ℤ), ⊤),
        (fixedFactorBoundaryIso iA F (tensorPowModule XA LA (n : ℤ))
          (fullGraphDivisorFrame k K z π j p hq s hs H d hd)).hom.app ⊤
            (pullbackGlobalSections iA _ aS) = pullbackGlobalSections iA _ bS ∧
        zeroScheme _ ((Modules.pullback iA).obj (tensorModules F (tensorPowModule XA LA (n : ℤ))))
          (pullbackGlobalSections iA _ aS) = ⊤ ∧
        zeroScheme _ ((Modules.pullback iA).obj (tensorPowModule XA LA (n : ℤ)))
          (pullbackGlobalSections iA _ bS) = ⊤ := by
  letI : Smooth (j ≫ π) := SmoothOfRelativeDimension.smooth 1 (j ≫ π)
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π)
  letI := fullGraphBoundary_isClosedImmersion π j d s hd
  have hLA : IsAmple XA LA :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (pullback.snd (j ≫ π) π) L hL
  obtain ⟨eL⟩ := nonempty_lambdaCoefficientBoundaryFrame π j s d L
  obtain ⟨N, hN⟩ := exists_eventually_normalized_boundary_sections iA
    (pullback.fst (j ≫ π) π) LA hLA F
    (fullGraphDivisorFrame k K z π j p hq s hs H d hd)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨en⟩ := Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_pullback_tensorPower
    iA LA ⟨eL⟩ (n : ℤ)
  exact hN n hn en

variable (a : A ⟶ Spec (.of k[X])) [IsOpenImmersion a]
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark k K z)))

local notation "XN" => pullback (a ≫ coordinateLineProjection k) π
local notation "LN" => (Modules.pullback (pullback.snd (a ≫ coordinateLineProjection k) π)).obj L
local notation "iN" => psiBoundaryInclusion (coordinateLineProjection k) π j p hq a
  (coordinateMark k K z) s hs d

/-- Produce the actual second pair on the entire independent correction source
A. The field-boundary frame avoids any principal-open or dense-open substitution. -/
theorem exists_eventually_wholeField_scalar_sections :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ nS dS : Γ(tensorPowModule XN LN (n : ℤ), ⊤),
        pullbackGlobalSections iN _ nS =
          correctionFullBoundaryCoordinate k K z π d a ha • pullbackGlobalSections iN _ dS ∧
        zeroScheme _ ((Modules.pullback iN).obj (tensorPowModule XN LN (n : ℤ)))
          (pullbackGlobalSections iN _ nS) = ⊤ ∧
        zeroScheme _ ((Modules.pullback iN).obj (tensorPowModule XN LN (n : ℤ)))
          (pullbackGlobalSections iN _ dS) = ⊤ := by
  letI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian a
  letI := psiBoundary_closed (coordinateLineProjection k) π j p hq a
    (coordinateMark k K z) s hs d hd
  have hLN : IsAmple XN LN :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom
      (pullback.snd (a ≫ coordinateLineProjection k) π) L hL
  obtain ⟨eL⟩ := nonempty_psiCoefficientBoundaryFrame π j s d L
    (coordinateLineProjection k) p hq a (coordinateMark k K z) hs
  obtain ⟨N, hN⟩ := exists_eventually_scalar_boundary_sections
    (pullback.fst (a ≫ coordinateLineProjection k) π) LN hLN iN
    (correctionFullBoundaryUnit k K z π d a ha)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨en⟩ := Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_pullback_tensorPower
    iN LN ⟨eL⟩ (n : ℤ)
  exact hN n hn en

end AlgebraicGeometry.Scheme.RelativeCurvePencil
