/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ChartBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionBoundaryMaps
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FullBoundary

/-!
# The source correction at the whole infinity boundary

The full inverse infinity boundary factors through the original infinity
leg of the correction boundary. The prescribed correction scalar is one
on that leg.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X A Z C P Y D₁ D₂ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) (f : C ⟶ P) (j : Y ⟶ C)
  (p : Y ⟶ X) (hB : j ≫ (f ≫ π) = p ≫ q)
  (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (d₂ : D₂ ⟶ P)
  (ha : Disjoint (Set.range a) (Set.range z))
  (U : (pullback (a ≫ q) π : Scheme.{u}).Opens)

local notation "b" => (a ≫ q)
local notation "F" => (retainedProductInclusion b π f)
local notation "mI" => (retainedProductInclusion b π d₂)
local notation "iN" => (psiBoundaryInclusion q (f ≫ π) j p hB a z s hs d₁)
local notation "θN" => (fullCorrectionCoordinate q (f ≫ π) z e d₁ a ha)

/-- The source chart restricts along the actual inverse infinity factor. -/
theorem exists_correctionSourceInfinity_factor
    (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)
    (l : pullback b (d₂ ≫ π) ⟶ U.toScheme) (hl : l ≫ U.ι = mI) :
    ∃ v : pullback F mI ⟶ pullback (pullback.snd b (f ≫ π)) d₁ ⨿ pullback b (z ≫ q),
      normQuotientBoundaryMap F U mI l hl ≫ pullback.fst F U.ι = v ≫ iN ∧
        v.appTop θN = 1 := by
  obtain ⟨v, hv⟩ := exists_productInverseBoundary_factor b π f d₁ d₂ bI hbI
  refine ⟨v ≫ coprod.inl, ?_, ?_⟩
  · rw [normQuotientBoundaryMap_fst]
    simpa only [Category.assoc, psiBoundaryInclusion, coprod.inl_desc] using hv
  · rw [Hom.comp_appTop, CommRingCat.comp_apply, fullCorrectionCoordinate_infinity, map_one]

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
