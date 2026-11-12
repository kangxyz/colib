/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ChartBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionBoundaryMaps
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.NormBoundaryCoordinates

/-!
# The correction parameter on the whole target boundary

The infinity and marked maps factor through the original boundary and
preserve its prescribed coordinates.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option showPartialSyntaxErrors true

open CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X P A Z D₂ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (hA : jA ≫ π = (𝟙 X) ≫ q) (a : A ⟶ X) (z : Z ⟶ X)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₂ : D₂ ⟶ P) (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (U : (pullback (a ≫ q) π : Scheme.{u}).Opens)

local notation "b" => (a ≫ q)
local notation "zA" => (z ≫ jA)
local notation "hA₀" => (hA.trans (Category.id_comp q))
local notation "τ" => (correctionTargetParameterMap q π jA hA₀ a)
local notation "iA" => (fullGraphBoundaryMap π jA z d₂)
local notation "θA" => (fullGraphCoordinate q π jA (𝟙 X) hA z z (Category.comp_id z)
  IsPullback.of_id_snd e d₂ hd₂)
local notation "mI" => (retainedProductInclusion b π d₂)
local notation "mZ" => (retainedProductInclusion b π zA)
local notation "u₂" => (Scheme.Opens.ι U ≫ τ)

/-- The target infinity map factors through the original boundary, where
the prescribed scalar is one. -/
theorem exists_correctionTargetInfinity_factor
    (l : pullback b (d₂ ≫ π) ⟶ U.toScheme) (_hl : l ≫ U.ι = mI) :
    ∃ v : pullback b (d₂ ≫ π) ⟶
        pullback (pullback.snd (jA ≫ π) π) d₂ ⨿ pullback (jA ≫ π) (z ≫ jA ≫ π),
      l ≫ u₂ = v ≫ iA ∧ v.appTop θA = 1 := by
  obtain ⟨v, hv⟩ := exists_productTargetBoundary_factor b π (jA ≫ π) τ
    (correctionTargetParameterMap_snd q π jA hA₀ a) d₂
  refine ⟨v ≫ coprod.inl, ?_, ?_⟩
  · rw [← Category.assoc l, _hl]
    simpa only [Category.assoc, fullGraphBoundaryMap, coprod.inl_desc, infinityProductMap]
      using hv
  · rw [Hom.comp_appTop, CommRingCat.comp_apply, fullGraphCoordinate_infinity, map_one]

/-- The target marked map factors through the original boundary and reads
the actual graph coordinate from its marked leg. -/
theorem exists_correctionTargetMark_factor {B : Scheme.{u}}
    (l : B ⟶ U.toScheme) (α : B ⟶ pullback b (zA ≫ π)) (_hl : l ≫ U.ι = α ≫ mZ) :
    ∃ v : B ⟶ pullback (pullback.snd (jA ≫ π) π) d₂ ⨿ pullback (jA ≫ π) (z ≫ jA ≫ π),
      l ≫ u₂ = v ≫ iA ∧
        v.appTop θA = (α ≫ (correctionMarkBaseIso q π jA hA₀ a z).hom).appTop
          (correctionCoordinate q z e a) := by
  let v := α ≫ correctionMarkToTargetProduct q π jA hA₀ a z
  let m := markedProductToTarget q π jA (𝟙 X) hA z z (Category.comp_id z)
  refine ⟨v ≫ coprod.inr, ?_, ?_⟩
  · rw [← Category.assoc l, _hl]
    simp only [v, Category.assoc, fullGraphBoundaryMap, coprod.inr_desc,
      correctionMarkToTargetProduct_map]
  · rw [Hom.comp_appTop, CommRingCat.comp_apply, fullGraphCoordinate_mark,
      ← CommRingCat.comp_apply, ← Hom.comp_appTop]
    change ((α ≫ correctionMarkToTargetProduct q π jA hA₀ a z) ≫ m).appTop
      (targetCoordinate q z e) = _
    rw [Category.assoc, show correctionMarkToTargetProduct q π jA hA₀ a z ≫ m =
      (correctionMarkBaseIso q π jA hA₀ a z).hom ≫ correctionProductToTarget q z a from
        correctionMarkToTargetProduct_coordinate q π jA hA₀ a z,
      ← Category.assoc, Hom.comp_appTop, CommRingCat.comp_apply]
    rfl

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
