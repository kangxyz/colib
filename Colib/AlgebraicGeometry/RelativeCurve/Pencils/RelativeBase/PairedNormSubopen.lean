/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.GlobalSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.AssociatedBoundaryUnit
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionBoundaryMaps
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormAssociation
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormUnitData

/-!
# Association of the paired graph ratios on one affine subopen

The same graph coefficients restrict through the actual finite pullback.
Their affine association unit has value one on both full boundary schemes.
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

local instance {U : Scheme.{u}} (L : U.Modules) [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
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
  (bI : pullback f d₂ ⟶ D₁) (U : (pullback (j ≫ f ≫ π) π : Scheme.{u}).Opens)

local notation "w₁" => (pullback.fst F (Scheme.Opens.ι U))
local notation "w₂" => (Scheme.Opens.ι U ≫ κ)
local notation "g" => (pullback.snd F (Scheme.Opens.ι U))

set_option maxHeartbeats 1000000 in
-- Restriction uses the actual chosen double pullback and both graph sections.
/-- An affine subopen gives the prescribed association and its boundary values. -/
theorem exists_pairedNormAssociationUnit_on_affineSubopen
    [hFinite : IsFiniteLocallyFree (graphProductMap π f j)] (hF : IsFiniteLocallyFree g)
    (V : U.toScheme.Opens)
    (cB : Γ((pullback F U.ι : Scheme.{u}), ⊤)) (cA : Γ(U.toScheme, ⊤)) :
    bI ≫ d₁ = pullback.fst f d₂ →
    IsAffineOpen V → IsFreeNormChart F (V.ι ≫ U.ι) →
    PairedNormChartResidualFactor π f j jA p hRet z s H (V.ι ≫ U.ι) d₁ →
    @PairedGraphRatioWitness (pullback b (f ≫ π)) (pullback F U.ι) w₁
      Δ₁ (compactificationGraphIdeal_isEffectiveCartierDivisor (f ≫ π) j)
      c₁.T c₁.T_invertible c₁.aS c₁.bS cB →
    @PairedGraphRatioWitness (pullback (jA ≫ π) π) U.toScheme w₂
      Δ₂ (compactificationGraphIdeal_isEffectiveCartierDivisor π jA)
      c₂.T c₂.T_invertible c₂.aS c₂.bS cA →
    NormAssociationOnRestriction F U hF mI mZ cB cA V :=
  fun hbI hV hFree hResidual hBcoeff hAcoeff ↦
    letI : IsFiniteLocallyFree g := hF
    letI : IsAffine V.toScheme := hV
    let w : V.toScheme ⟶ pullback (j ≫ f ≫ π) π := V.ι ≫ U.ι
    let gx := pullback.snd F w
    letI : IsFiniteLocallyFree gx := isFiniteLocallyFree_pullback_snd F w hFinite
    letI : Algebra Γ(V.toScheme, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) :=
      gx.appTop.hom.toAlgebra
    letI : Module.Free Γ(V.toScheme, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) := hFree
    let u := normQuotientBoundaryMap F U w V.ι rfl
    have hu : u ≫ w₁ = pullback.fst F w := normQuotientBoundaryMap_fst F U w V.ι rfl
    have hx : IsPullback u gx g V.ι := normQuotientBoundaryMap_isPullback F U w V.ι rfl
    have hv : V.ι ≫ w₂ = w ≫ κ := (Category.assoc _ _ _).symm
    letI := c₁.T_invertible
    letI := c₂.T_invertible
    have hB' := PairedGraphRatioWitness.pullback w₁ u (pullback.fst F w) hu
      Δ₁ c₁.T c₁.aS c₁.bS cB hBcoeff
    have hA' := PairedGraphRatioWitness.pullback w₂ V.ι (w ≫ κ) hv
      Δ₂ c₂.T c₂.aS c₂.bS cA hAcoeff
    let Hchart := exists_pairedNormAssociationUnit_on_chart q π f j jA p hRet
      hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ w bI hbI hResidual
      hB'.numerator hA'.numerator (u.appTop cB) (V.ι.appTop cA)
      hB'.pole hA'.pole hB'.coefficient hA'.coefficient hFree
    Hchart.elim fun μ hμ ↦
      ⟨μ, (normTop_appTop_of_isPullback g gx u V.ι hx cB).symm.trans
          ((normTop_eq_affineNorm gx (u.appTop cB)).trans hμ.1),
        hμ.2.1, hμ.2.2⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
