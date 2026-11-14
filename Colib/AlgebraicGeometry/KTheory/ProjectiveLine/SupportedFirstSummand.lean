/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TwoSummands
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedFlatPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenBoundaryNaturality

/-! # The untwisted projective-line summand with support

The untwisted summand restricts to the supported full subcategories for the
literal inverse-image open. Forgetting support retains the ambient flat pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (U : X.Opens)

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "V" => Functor.obj
  (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom π)))) U
local notation "q" => supportRestrictionPair π U
local notation "j" => Scheme.Opens.ι V

/-- The restricted projective-line projection is flat. -/
theorem projectiveLineSupportRestriction_flat_left : Flat (q).left := by
  change Flat ((π).resLE U (V) le_rfl)
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The supported first summand is the actual flat pullback on the inverse-image pair. -/
def projectiveLineSupportedFirstSummand :
    (perfectSupported U.ι).FullSubcategory ⥤ (perfectSupported j).FullSubcategory := by
  let : Flat (q).left := projectiveLineSupportRestriction_flat_left X U
  let : Flat (q).right := inferInstanceAs (Flat π)
  exact perfectSupportedFlatPairPullback q

/-- The supported first summand is exact for the native supported Waldhausen structures. -/
theorem projectiveLineSupportedFirstSummand_exact :
    IsExact (perfectSupportedWaldhausen U.ι).cof (perfectSupportedWaldhausen U.ι).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (projectiveLineSupportedFirstSummand X U) := by
  let : Flat (q).left := projectiveLineSupportRestriction_flat_left X U
  let : Flat (q).right := inferInstanceAs (Flat π)
  exact perfectSupportedFlatPairPullback_exact q

/-- Pullback along the actual restricted projection. -/
def projectiveLineOpenFirstSummand :
    ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := U.toScheme.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (Scheme.Opens.toScheme V).toRingedSpace)) := by
  let : Flat ((π).resLE U (V) le_rfl) := projectiveLineSupportRestriction_flat_left X U
  exact perfectFlatPullback ((π).resLE U (V) le_rfl)

/-- Flat pullback on the inverse-image open is Waldhausen exact. -/
theorem projectiveLineOpenFirstSummand_exact :
    IsExact (RingedSpace.perfectComplexesWaldhausen U.toScheme.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen U.toScheme.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen (Scheme.Opens.toScheme V).toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen (Scheme.Opens.toScheme V).toRingedSpace).weq
      (projectiveLineOpenFirstSummand X U) := by
  let : Flat ((π).resLE U (V) le_rfl) := projectiveLineSupportRestriction_flat_left X U
  exact perfectFlatPullback_waldhausenExact ((π).resLE U (V) le_rfl)

/-- The ordinary first summand commutes with restriction to the actual inverse-image open. -/
def projectiveLineFirstSummand_restrictIso :
    projectiveLineFirstSummand X ⋙ perfectComplexesRestrictOpenImmersion j ≅
      perfectComplexesRestrictOpenImmersion U.ι ⋙ projectiveLineOpenFirstSummand X U := by
  let : Flat (q).left := projectiveLineSupportRestriction_flat_left X U
  apply perfectOpenRestrictIso_of_complexIso U.ι j
  exact Functor.isoWhiskerLeft
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (pullbackComplexOpenPairIso q)

/-- The untwisted summand is coarse exact for the actual open restriction weak classes. -/
theorem projectiveLineFirstSummand_coarseExact :
    IsExact (perfectOpenWeakWaldhausen U.ι).cof (perfectOpenWeakWaldhausen U.ι).weq
      (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
      (projectiveLineFirstSummand X) :=
  perfectOpen_coarseExact_of_restrictIso U.ι j (projectiveLineFirstSummand_exact X)
    (projectiveLineOpenFirstSummand_exact X U) (projectiveLineFirstSummand_restrictIso X U)

/-- The supported untwisted summand intertwines the canonical relative boundaries. -/
theorem projectiveLineSupportedFirstSummand_connecting (n : ℕ) :
    (KMap (projectiveLineSupportedFirstSummand_exact X U) n).comp
      (perfectOpenConnectingHom U.ι n) =
    (perfectOpenConnectingHom j n).comp
      (KMap (projectiveLineFirstSummand_coarseExact X U) (n + 1)) :=
  perfectOpenConnectingHom_natural U.ι j (projectiveLineFirstSummand_exact X)
    (projectiveLineFirstSummand_coarseExact X U) (projectiveLineSupportedFirstSummand_exact X U)
    n (Iso.refl _)

end AlgebraicGeometry.Scheme
