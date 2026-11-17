/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ComplementComparison
import Colib.AlgebraicGeometry.Scheme.CartesianRange

/-!
# Original products of closed supports

The product of the original open complements is the open complement of
the corresponding product of the closed support with the smooth parameter.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable {k : Type u} [Field k]

variable {Z V : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ V) [IsClosedImmersion i.left]

/-- The original inclusion of the support after taking an actual smooth product. -/
abbrev supportedProductInclusion (Y : SmoothSite (Spec (CommRingCat.of k))) :
    product Z Y ⟶ product V Y :=
  (Contraction.parameterProduct Y).map i

instance supportedProductInclusion_isClosedImmersion (Y : SmoothSite (Spec (CommRingCat.of k))) :
    IsClosedImmersion (supportedProductInclusion i Y).left := by
  have h : IsClosedImmersion i.left := inferInstance
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (Contraction.parameterProduct_map_isPullback Y i).flip h

/-- The product of this closed inclusion has the literal product of its
complementary open as its complement. -/
theorem range_parameterProduct_complement (Y : SmoothSite (Spec (CommRingCat.of k))) :
    Set.range ((Contraction.parameterProduct Y).map (closedPairOpenInclusion i.left)).left =
      Set.range (closedPairOpenInclusion (supportedProductInclusion i Y).left).left := by
  let ψ : (product V Y).left ⟶ V.left := (productFst V Y).left
  let j := closedPairOpenInclusion i.left
  have hj : Set.range ((Contraction.parameterProduct Y).map j).left =
      ψ ⁻¹' Set.range j.left :=
    Scheme.range_fst_of_isPullback (Contraction.parameterProduct_map_isPullback Y j)
  have hi : Set.range (supportedProductInclusion i Y).left = ψ ⁻¹' Set.range i.left :=
    Scheme.range_fst_of_isPullback (Contraction.parameterProduct_map_isPullback Y i)
  change Set.range ((Contraction.parameterProduct Y).map j).left =
    Set.range (closedPairOpenInclusion (supportedProductInclusion i Y).left).left
  calc
    _ = ψ ⁻¹' Set.range j.left := hj
    _ = ψ ⁻¹' (Set.range i.left)ᶜ := congrArg (ψ ⁻¹' ·) (range_closedPairOpenInclusion i.left)
    _ = (ψ ⁻¹' Set.range i.left)ᶜ := Set.preimage_compl
    _ = (Set.range (supportedProductInclusion i Y).left)ᶜ := congrArg (·ᶜ) hi.symm
    _ = _ := (range_closedPairOpenInclusion (supportedProductInclusion i Y).left).symm

/-- The original open product inclusion presents the complement of the closed product support. -/
def supportedProductComplementArrowIso (Y : SmoothSite (Spec (CommRingCat.of k))) :
    ((Contraction.parameterProduct Y).mapArrow.obj (Arrow.mk (closedPairOpenInclusion i.left))) ≅
      Arrow.mk (closedPairOpenInclusion (supportedProductInclusion i Y).left) :=
  openInclusionArrowIso ((Contraction.parameterProduct Y).map (closedPairOpenInclusion i.left))
    (closedPairOpenInclusion (supportedProductInclusion i Y).left)
    (range_parameterProduct_complement i Y)

end AlgebraicGeometry.MotivicHomotopy
