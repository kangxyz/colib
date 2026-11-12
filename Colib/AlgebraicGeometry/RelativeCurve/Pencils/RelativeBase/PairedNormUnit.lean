/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormUnitDomain

/-!
# The original paired norm unit on the whole boundary neighborhood

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

local instance pairedNormUnitModules {U : Scheme.{u}} (L : U.Modules)
    [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance pairedNormUnitDivisor {U : Scheme.{u}} (D : U.IdealSheafData)
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

set_option maxHeartbeats 1200000 in
-- The whole open carries both original numerator generation proofs.
/-- The two original pairs produce the normalized quotient on an actual open
containing both whole boundaries, with the exact native norm equation. -/
theorem exists_pairedNormUnit
    [hFinite : IsFiniteLocallyFree (graphProductMap π f j)]
    [hSep : IsSeparated (terminal.from (pullback (j ≫ f ≫ π) π : Scheme.{u}))]
    (hSrc : SourceMarkedBoundaryGeneration π f j zA s d₁) :
    bI ≫ d₁ = pullback.fst f d₂ →
    (∀ (T : Scheme.{u}) (w : T ⟶ pullback (j ≫ f ≫ π) π),
      PairedNormChartResidualFactor π f j jA p hRet z s H w d₁) →
    HasPairedNormUnit q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ :=
  fun hbI hResidual ↦
    letI := c₁.T_invertible
    letI := c₂.T_invertible
    match exists_pairedNormUnitDomain q π f j jA p hRet hB hA a z s hs H e
      d₁ hd₁ d₂ hd₂ ha c₁ c₂ bI hbI hSrc with
    | ⟨V, ⟨hI, ⟨hZ, ⟨ha₁, ⟨hb₁, ⟨ha₂, hb₂⟩⟩⟩⟩⟩⟩ =>
      have h : terminal.from V.toScheme = V.ι ≫ terminal.from (pullback b π) :=
        terminal.hom_ext _ _
      letI : IsSeparated (terminal.from V.toScheme) :=
        (congrArg IsSeparated h).mpr
          (IsSeparated.stableUnderComposition.comp_mem V.ι (terminal.from (pullback b π))
            (IsSeparated.isSeparated_of_mono V.ι) hSep)
      have hV : IsFiniteLocallyFree (pullback.snd F V.ι) :=
        @isFiniteLocallyFree_pullback_snd (pullback b (f ≫ π)) V.toScheme (pullback b π)
          F V.ι hFinite
      let cB : Γ((pullback F V.ι : Scheme.{u}), ⊤) :=
        graphSectionRatioCoefficientOfGenerating (pullback.fst F V.ι) Δ₁ c₁.T c₁.aS c₁.bS ha₁
      let cA : Γ(V.toScheme, ⊤) :=
        graphSectionRatioCoefficientOfGenerating (V.ι ≫ κ) Δ₂ c₂.T c₂.aS c₂.bS ha₂
      have hQuotient : @NormQuotientOnBoundaries (pullback F V.ι) (pullback b π)
          (pullback b (d₂ ≫ π)) (pullback b (zA ≫ π)) V (pullback.snd F V.ι) hV mI mZ cB cA :=
        exists_pairedNormUnit_on_open q π f j jA p hRet hB hA
          a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ bI V (hFinite := hFinite) hV cB cA
          hbI hI hZ hResidual ⟨ha₁, hb₁, rfl⟩ ⟨ha₂, hb₂, rfl⟩
      ⟨V, hV, ha₁, ha₂, hQuotient⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
