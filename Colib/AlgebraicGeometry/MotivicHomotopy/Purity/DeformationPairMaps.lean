/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ClosedPair
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationSmooth
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleSmooth
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalSupport

/-!
# The two deformation maps of smooth closed pairs

The ambient deformation and its closed support are smooth-site objects over the
original base. The two fibre maps induce squares on the open complements of
the closed supports.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Conormal Stacks.Deformation

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {Z X : SmoothSite S}

/-- The zero-ideal deformation of the centre, with its original projection to the base. -/
def deformationSupport (Z : SmoothSite S) : SmoothSite S := by
  let J : Z.left.IdealSheafData := ⊥
  have := smoothOfRelativeDimension_deformationSpaceToBase_bot Z.left
  have : Smooth (deformationSpaceToBase J) :=
    SmoothOfRelativeDimension.smooth 1 (deformationSpaceToBase J)
  have : IsAffineHom (deformationSpaceToBase J) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (extReesAlgebraSheaf J)
  exact mk (deformationSpaceToBase J ≫ Z.hom)

variable (i : Z ⟶ X) [IsClosedImmersion i.left]

/-- The composite structure map of the centre is its smooth structure map. -/
theorem smooth_closedPair_comp (i : Z ⟶ X) : Smooth (i.left ≫ X.hom) := by
  rw [MorphismProperty.Over.w i]
  infer_instance

/-- The original extended-Rees deformation of the smooth closed pair. -/
def closedPairDeformation : SmoothSite S := by
  have := smooth_closedPair_comp i
  have := isIso_coborderRange_ι_of_isClosedImmersion i.left
  have : IsAffineHom (deformationSpaceToBase (coborderIdeal i.left)) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase
      (extReesAlgebraSheaf (coborderIdeal i.left))
  have := smooth_deformationSpaceToBase_comp_of_isClosedImmersion i.left X.hom
  exact mk (deformationSpaceToBase (coborderIdeal i.left) ≫ (i.left.coborderRange.ι ≫ X.hom))

/-- The original closed support inclusion, viewed as a map of smooth-site objects. -/
def deformationSupportInclusion : deformationSupport Z ⟶ closedPairDeformation i :=
  homMk (deformationSupportMap i.left) (by
    change deformationSupportMap i.left ≫
      (deformationSpaceToBase (coborderIdeal i.left) ≫ (i.left.coborderRange.ι ≫ X.hom)) =
      deformationSpaceToBase (⊥ : Z.left.IdealSheafData) ≫ Z.hom
    rw [← Category.assoc, deformationSupportMap_toBase, Category.assoc, ← Category.assoc
      i.left.liftCoborder i.left.coborderRange.ι X.hom, Scheme.Hom.liftCoborder_ι,
      MorphismProperty.Over.w i])

instance isClosedImmersion_deformationSupportInclusion :
    IsClosedImmersion (deformationSupportInclusion i).left :=
  inferInstanceAs (IsClosedImmersion (deformationSupportMap i.left))

/-- The original ambient fibre-one map in the smooth site. -/
def deformationOneMap : X ⟶ closedPairDeformation i :=
  homMk (closedPairOneSection i.left) (by
    change closedPairOneSection i.left ≫
      (deformationSpaceToBase (coborderIdeal i.left) ≫ (i.left.coborderRange.ι ≫ X.hom)) =
      X.hom
    simp only [closedPairOneSection_toAmbient_assoc])

/-- The original one section of the deformation support in the smooth site. -/
def deformationSupportOneMap (Z : SmoothSite S) : Z ⟶ deformationSupport Z :=
  homMk (deformationOneSection (⊥ : Z.left.IdealSheafData)) (by
    change deformationOneSection (⊥ : Z.left.IdealSheafData) ≫
      (deformationSpaceToBase (⊥ : Z.left.IdealSheafData) ≫ Z.hom) = Z.hom
    simp only [deformationOneSection_toBase_assoc])

/-- The original zero section of the deformation support in the smooth site. -/
def deformationSupportZeroMap (Z : SmoothSite S) : Z ⟶ deformationSupport Z :=
  homMk (deformationZeroSectionBot Z.left) (by
    change deformationZeroSectionBot Z.left ≫
      (deformationSpaceToBase (⊥ : Z.left.IdealSheafData) ≫ Z.hom) = Z.hom
    simp only [deformationZeroSectionBot_toBase_assoc])

variable {n m : ℕ}

/-- The actual normal-bundle fibre map in the smooth site. -/
def deformationNormalMapOfSmooth : normalBundleOfSmooth i ⟶ closedPairDeformation i := by
  have := smooth_closedPair_comp i
  refine homMk (normalBundleToDeformation i.left X.hom) ?_
  change normalBundleToDeformation i.left X.hom ≫
    (deformationSpaceToBase (coborderIdeal i.left) ≫ (i.left.coborderRange.ι ≫ X.hom)) =
    normalBundleToBase i.left ≫ Z.hom
  simp only [normalBundleToDeformation_toAmbient_assoc, MorphismProperty.Over.w i]

/-- Pure pairs use the same normal-bundle fibre map. -/
abbrev deformationNormalMap (_hX : RelativeDimension X.hom n)
    (_hZ : RelativeDimension Z.hom m) : normalBundleOfSmooth i ⟶ closedPairDeformation i :=
  deformationNormalMapOfSmooth i

section Squares

/-- The original cartesian support square at parameter one. -/
theorem deformationOneSupportSquare :
    IsPullback i.left (deformationSupportOneMap Z).left (deformationOneMap i).left
      (deformationSupportInclusion i).left :=
  isPullback_closedPairOneSection_support i.left

/-- The original cartesian support square at parameter zero. -/
theorem deformationZeroSupportSquare :
    IsPullback (normalBundleZeroSectionOfSmooth i).left (deformationSupportZeroMap Z).left
      (deformationNormalMapOfSmooth i).left (deformationSupportInclusion i).left := by
  let := smooth_closedPair_comp i
  exact isPullback_normalBundleToDeformation_support i.left X.hom

variable [IsNoetherian S]

/-- The square of open complements induced by the original fibre-one inclusion. -/
def deformationOneSquare : Square (SmoothSite S) :=
  closedPairSquare (z := i.left) (w := (deformationSupportInclusion i).left)
    (f := deformationOneMap i) (deformationOneSupportSquare i)

/-- The square of open complements induced by the actual normal-bundle fibre inclusion. -/
def deformationZeroSquareOfSmooth : Square (SmoothSite S) :=
  closedPairSquare (z := (normalBundleZeroSectionOfSmooth i).left)
    (w := (deformationSupportInclusion i).left) (f := deformationNormalMapOfSmooth i)
    (deformationZeroSupportSquare i)

/-- Pure pairs use the same square of open complements at zero. -/
abbrev deformationZeroSquare (_hX : RelativeDimension X.hom n)
    (_hZ : RelativeDimension Z.hom m) : Square (SmoothSite S) := deformationZeroSquareOfSmooth i

/-- The open-complement square at one is cartesian. -/
theorem deformationOneSquare_isPullback : (deformationOneSquare i).IsPullback :=
  closedPairSquare_isPullback (z := i.left) (w := (deformationSupportInclusion i).left)
    (f := deformationOneMap i) (deformationOneSupportSquare i)

/-- The open-complement square at zero is cartesian. -/
theorem deformationZeroSquare_isPullback (hX : RelativeDimension X.hom n)
    (hZ : RelativeDimension Z.hom m) : (deformationZeroSquare i hX hZ).IsPullback :=
  closedPairSquare_isPullback (z := (normalBundleZeroSectionOfSmooth i).left)
    (w := (deformationSupportInclusion i).left) (f := deformationNormalMapOfSmooth i)
    (deformationZeroSupportSquare i)

end Squares

end AlgebraicGeometry.Scheme.SmoothSite

end
