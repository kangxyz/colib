/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionCoefficient
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionData

/-!
# The two boundary values of an original normalized pair

The coefficient on a chart takes value one on any pullback of the complete
infinity boundary. On the full marked factor, its value is the original
target graph coordinate. Both facts apply to the chosen section pair.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Boundary/SectionPairGraphMarkedNorm.lean`
and `SectionPairGraphInfinityNorm.lean` in the same directory
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance]
  compactificationGraphIdeal_isEffectiveCartierDivisor
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

local instance {U : Scheme.{u}} (L : U.Modules) [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S X C Y Z D A W B : Scheme.{u}} (q : X ⟶ S)
  [IsSeparated q] [SmoothOfRelativeDimension 1 q] (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a : A ⟶ X) (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range z))

local notation "Dg" => (Hom.ker (compactificationGraph π j))
local notation "iA" => (fullGraphBoundaryMap π j s d)
local notation "iI" => (infinityProductMap π j d)
local notation "iZ" => (markedProductMap π j s)

variable (c : SectionData q π j p hq a z s hs H e d hd ha)
  (g : W ⟶ pullback (j ≫ π) π)

local notation "L" => (Stacks.Divisors.tensorModules (divisorSheaf Dg) (SectionData.T c))

/-- Both original sections generate on any specified factorization through
the entire boundary. -/
theorem SectionData.generators_on_boundary_factor
    (v : W ⟶ pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π))
    (h : v ≫ iA = g) :
    letI := c.T_invertible
    zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L c.aS) = ⊤ ∧
      zeroScheme W ((Modules.pullback g).obj c.T) (pullbackGlobalSections g c.T c.bS) = ⊤ := by
  let := c.T_invertible
  exact ⟨zeroScheme_pullback_eq_top_of_factor iA g v h L c.aS c.numerator_zero,
    zeroScheme_pullback_eq_top_of_factor iA g v h c.T c.bS c.denominator_zero⟩

/-- On the entire infinity summand, the chart coefficient has value one. -/
theorem SectionData.graphSectionRatioCoefficient_on_infinity
    (i : B ⟶ W) (v : B ⟶ pullback (pullback.snd (j ≫ π) π) d)
    (h : i ≫ g = v ≫ iI) :
    letI := c.T_invertible
    ∀ hgen : zeroScheme W ((Modules.pullback g).obj L)
        (pullbackGlobalSections g L c.aS) = ⊤,
      i.appTop (graphSectionRatioCoefficient g Dg c.T c.aS c.bS hgen) = 1 := by
  let := c.T_invertible
  intro hgen
  have hi : i ≫ g = (v ≫ coprod.inl) ≫ iA := by
    simpa only [Category.assoc, fullGraphBoundaryMap, coprod.inl_desc] using h
  rw [graphSectionRatioCoefficient_boundary g Dg c.T iA i (v ≫ coprod.inl) hi
    (fullGraphFrame q π j p hq z s hs H e d hd) c.aS c.bS hgen c.normalized]
  change (v ≫ coprod.inl).appTop (fullGraphCoordinate q π j p hq z s hs H e d hd) = 1
  rw [Hom.comp_appTop, CommRingCat.comp_apply, fullGraphCoordinate_infinity, map_one]

/-- On the entire marked summand, the chart coefficient has the original
target graph coordinate under the actual pullback map. -/
theorem SectionData.graphSectionRatioCoefficient_on_mark
    (i : B ⟶ W) (v : B ⟶ pullback (j ≫ π) (s ≫ j ≫ π))
    (h : i ≫ g = v ≫ iZ) :
    letI := c.T_invertible
    ∀ hgen : zeroScheme W ((Modules.pullback g).obj L)
        (pullbackGlobalSections g L c.aS) = ⊤,
      i.appTop (graphSectionRatioCoefficient g Dg c.T c.aS c.bS hgen) =
        (v ≫ markedProductToTarget q π j p hq z s hs).appTop (targetCoordinate q z e) := by
  let := c.T_invertible
  intro hgen
  have hi : i ≫ g = (v ≫ coprod.inr) ≫ iA := by
    simpa only [Category.assoc, fullGraphBoundaryMap, coprod.inr_desc] using h
  rw [graphSectionRatioCoefficient_boundary g Dg c.T iA i (v ≫ coprod.inr) hi
    (fullGraphFrame q π j p hq z s hs H e d hd) c.aS c.bS hgen c.normalized]
  change (v ≫ coprod.inr).appTop (fullGraphCoordinate q π j p hq z s hs H e d hd) = _
  rw [Hom.comp_appTop, CommRingCat.comp_apply, fullGraphCoordinate_mark,
    Hom.comp_appTop, CommRingCat.comp_apply]

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
