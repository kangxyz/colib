/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CoefficientFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeBoundaryClosed
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedBoundarySections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.ScalarBoundarySections
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
/-!
# Actual relative Serre sections on both complete refined sources

This intermediate theorem consumes the actual common-neighborhood frames from
RelativeBase.CanonicalFrame. It does not use absolute properness over the ground
field. The compactification is proper only over the given affine Noetherian base.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.AlgebraicGeometry.RelativeSerreVanishing
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens
  compactificationGraphIdeal_isEffectiveCartierDivisor
local instance (Y : Scheme.{u}) (M : Y.Modules) [hM : IsInvertibleModule Y M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M := hM

variable {S X C Y A Z D : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
  [IsAffine Y] [IsAffine A]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d : D ⟶ C) [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L)
  (eD : (Modules.pullback d).obj L ≅ SheafOfModules.unit D.ringCatSheaf)
  (eZ : (Modules.pullback (s ≫ j)).obj L ≅ SheafOfModules.unit Z.ringCatSheaf)

local notation "XA" => pullback (j ≫ π) π
local notation "LA" => CategoryTheory.Functor.obj (Modules.pullback (pullback.snd (j ≫ π) π)) L
local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "iA" => fullGraphBoundaryMap π j s d

include hL eD eZ in
/-- Produce the actual first pair for every sufficiently large coefficient
power on the unchanged original lambda product. -/
theorem exists_eventually_relative_normalized_sections :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ aS : Γ(tensorModules F (tensorPowModule XA LA (n : ℤ)), ⊤),
      ∃ bS : Γ(tensorPowModule XA LA (n : ℤ), ⊤),
        (fixedFactorBoundaryIso iA F (tensorPowModule XA LA (n : ℤ))
          (fullGraphFrame q π j p hq z s hs H e d hd)).hom.app ⊤
            (pullbackGlobalSections iA _ aS) = pullbackGlobalSections iA _ bS ∧
        @AlgebraicGeometry.zeroScheme _
          ((Modules.pullback iA).obj (tensorModules F (tensorPowModule XA LA (n : ℤ))))
          (pullbackTwistModule_isInvertible iA LA F (n : ℤ))
          (pullbackGlobalSections iA _ aS) = ⊤ ∧
        zeroScheme _ ((Modules.pullback iA).obj (tensorPowModule XA LA (n : ℤ)))
          (pullbackGlobalSections iA _ bS) = ⊤ := by
  let : Smooth (j ≫ π) := SmoothOfRelativeDimension.smooth 1 (j ≫ π)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π)
  let := fullGraphBoundary_isClosedImmersion π j d s hd
  let : IsAffineHom (pullback.snd (j ≫ π) π) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (j ≫ π) π) (isAffineHom_of_isAffine (j ≫ π))
  have hLA : IsAmple XA LA :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (pullback.snd (j ≫ π) π) L hL
  obtain ⟨eL⟩ := lambdaCoefficientFrame π j s d L eD eZ
  obtain ⟨N, hN⟩ := exists_eventually_normalized_boundary_sections iA
    (pullback.fst (j ≫ π) π) LA hLA F
    (fullGraphFrame q π j p hq z s hs H e d hd)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨en⟩ := exists_tensorPowModule_boundaryFrame iA LA eL (n : ℤ)
  exact hN n hn en

variable (a : A ⟶ X) [IsOpenImmersion a]
  (ha : Disjoint (Set.range a) (Set.range (z)))

local notation "XN" => pullback (a ≫ q) π
local notation "LN" => CategoryTheory.Functor.obj (Modules.pullback (pullback.snd (a ≫ q) π)) L
local notation "iN" => psiBoundaryInclusion (q) π j p hq a
  (z) s hs d

omit [IsAffine Y] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)] in
include hd hL eD eZ in
/-- Produce the actual second pair on the entire independent correction source
A. The intermediate frames come from the common principal-base construction. -/
theorem exists_eventually_relative_scalar_sections :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ nS dS : Γ(tensorPowModule XN LN (n : ℤ), ⊤),
        pullbackGlobalSections iN _ nS =
          fullCorrectionCoordinate q π z e d a ha • pullbackGlobalSections iN _ dS ∧
        zeroScheme _ ((Modules.pullback iN).obj (tensorPowModule XN LN (n : ℤ)))
          (pullbackGlobalSections iN _ nS) = ⊤ ∧
        zeroScheme _ ((Modules.pullback iN).obj (tensorPowModule XN LN (n : ℤ)))
          (pullbackGlobalSections iN _ dS) = ⊤ := by
  let : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian a
  let := psiBoundary_closed (q) π j p hq a
    (z) s hs d hd
  let : IsAffineHom (pullback.snd (a ≫ q) π) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (a ≫ q) π) (isAffineHom_of_isAffine (a ≫ q))
  have hLN : IsAmple XN LN :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom
      (pullback.snd (a ≫ q) π) L hL
  obtain ⟨eL⟩ := psiCoefficientFrame π j s d L eD eZ
    (q) p hq a (z) hs
  obtain ⟨N, hN⟩ := exists_eventually_scalar_boundary_sections
    (pullback.fst (a ≫ q) π) LN hLN iN
    (fullCorrectionUnit q π z e d a ha)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨en⟩ := exists_tensorPowModule_boundaryFrame iN LN eL (n : ℤ)
  exact hN n hn en

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
