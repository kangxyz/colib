/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.GlobalSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.AssociatedBoundaryUnit
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormUnitData
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormSubopen

/-!
# Gluing the paired norm unit on a specified open

The determinant association units of the original charts glue. Their inverse
is a regular unit with value one on the full target boundary, and its
multiplication equation retains the two actual coefficients.

Adapted from `SectionPairNormParameterNeighborhood.lean` under
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Norm` at
a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.Morphisms TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance]
  compactificationGraphIdeal_isEffectiveCartierDivisor
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

local instance pairedNormOpenModules {U : Scheme.{u}} (L : U.Modules)
    [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance pairedNormOpenDivisor {U : Scheme.{u}} (D : U.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S X Y P C A Z D₁ D₂ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] [SmoothOfRelativeDimension 1 π]
  (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P) (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)

local notation "b" => (j ≫ f ≫ π)
local notation "zA" => (z ≫ jA)
local notation "F" => (graphProductMap π f j)
local notation "κ" => (graphTargetParameterMap π f j jA p hRet)
local notation "Δ₁" => (Hom.ker (compactificationGraph (f ≫ π) j))
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "mI" => (retainedProductInclusion b π d₂)
local notation "mZ" => (retainedProductInclusion b π zA)

variable [IsClosedImmersion d₂] [IsClosedImmersion (z ≫ jA)]
  (bI : pullback f d₂ ⟶ D₁)
  (U : (pullback (j ≫ f ≫ π) π : Scheme.{u}).Opens)

local notation "w₁" => (pullback.fst F (Scheme.Opens.ι U))
local notation "w₂" => (Scheme.Opens.ι U ≫ κ)
local notation "g" => (pullback.snd F (Scheme.Opens.ι U))

set_option maxHeartbeats 1200000 in
-- All chart coefficients use the same original finite pullback and sections.
/-- The normalized norm quotient on the actual whole good open. The
coefficient equation holds for the canonical determinant norm on that open. -/
theorem exists_pairedNormUnit_on_open
    [hFinite : IsFiniteLocallyFree (graphProductMap π f j)]
    [hSepOpen : IsSeparated (terminal.from U.toScheme)] (hF : IsFiniteLocallyFree g)
    (cB : Γ((pullback F U.ι : Scheme.{u}), ⊤)) (cA : Γ(U.toScheme, ⊤)) :
    bI ≫ d₁ = pullback.fst f d₂ →
    Set.range mI ⊆ (U : Set (pullback (j ≫ f ≫ π) π : Scheme.{u})) →
    Set.range mZ ⊆ (U : Set (pullback (j ≫ f ≫ π) π : Scheme.{u})) →
    (∀ (T : Scheme.{u}) (w : T ⟶ pullback (j ≫ f ≫ π) π),
      PairedNormChartResidualFactor π f j jA p hRet z s H w d₁) →
    @PairedGraphRatioWitness (pullback b (f ≫ π)) (pullback F U.ι) w₁
      Δ₁ (compactificationGraphIdeal_isEffectiveCartierDivisor (f ≫ π) j)
      c₁.T c₁.T_invertible c₁.aS c₁.bS cB →
    @PairedGraphRatioWitness (pullback (jA ≫ π) π) U.toScheme w₂
      Δ₂ (compactificationGraphIdeal_isEffectiveCartierDivisor π jA)
      c₂.T c₂.T_invertible c₂.aS c₂.bS cA →
    @NormQuotientOnBoundaries (pullback F U.ι) (pullback b π)
      (pullback b (d₂ ≫ π)) (pullback b (zA ≫ π)) U g hF mI mZ cB cA :=
  fun hbI hI hZ hResidual hBcoeff hAcoeff ↦
    letI := c₂.T_invertible
    have hgraph : IsEffectiveCartierDivisor ((Δ₂).comap w₂) :=
      isEffectiveCartierDivisor_targetGraph_on_chart π f j jA p hRet U.ι
    have hChart (V : U.toScheme.Opens) (hV : IsAffineOpen V)
        (hFree : IsFreeNormChart F (V.ι ≫ U.ι)) :
        NormAssociationOnRestriction F U hF mI mZ cB cA V :=
      exists_pairedNormAssociationUnit_on_affineSubopen q π f j jA p hRet hB hA
        a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ bI U (hFinite := hFinite) hF V cB cA
        hbI hV hFree (hResidual V.toScheme (V.ι ≫ U.ι)) hBcoeff hAcoeff
    have hRegular (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
        IsRightRegular (V.ι.appTop cA) :=
      letI : IsAffine V.toScheme := hV
      PairedGraphRatioWitness.isRightRegular_appTop w₂ V.ι Δ₂
        (isPullbackDefined_of_flat V.ι _ hgraph) c₂.T c₂.aS c₂.bS cA hAcoeff
    @exists_normQuotientOnBoundaries_of_affine_association
      (pullback b (f ≫ π)) (pullback b π) (pullback b (d₂ ≫ π)) (pullback b (zA ≫ π))
      F hFinite U hSepOpen hF mI mZ hI hZ cB cA hChart hRegular

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
