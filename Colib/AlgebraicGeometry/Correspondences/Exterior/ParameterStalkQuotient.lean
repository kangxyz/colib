/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.CoefficientQuotient
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.PerfectFactor
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength

import Mathlib.Tactic.DSimpPercent

/-!
# Actual parameter equations in the native coefficient local ring

The diagonal coefficient inclusion has kernel the inverse-image ideal of the
actual diagonal. At every actual quotient point its stalk ring is the quotient
by the image of that diagonal ideal. The ring isomorphism identifies the quotient
map with the literal inclusion stalk map. Native smooth-section regularity and
flat base change supply a regular generating list of this exact kernel.

This is not a flatness assertion about the quotient map. Flatness concerns the
map from the original support-product stalk to this quotient stalk.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (Z : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "P" =>
  correspondenceSupportProduct (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
    (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
    (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "p" =>
  nativeExteriorCoefficientParameterPair X Y T z hz Z w hw

/-- The scheme-theoretic kernel is the actual diagonal inverse-image ideal. -/
theorem nativeExteriorParameterDiagonalInclusion_ker :
    (j).ker = (pullback.diagonal T.hom).ker.comap p := by
  calc
    (j).ker = ((pullbackSymmetry p (pullback.diagonal T.hom)).hom ≫ j).ker :=
      (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (pullback.fst p (pullback.diagonal T.hom)).ker := by simp
    _ = (pullback.diagonal T.hom).ker.comap p :=
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

/-- These are the actual parameter equations in the actual exterior coefficient stalk. -/
abbrev nativeExteriorParameterStalkIdeal (x : Q) : Ideal ((P).presheaf.stalk (j x)) :=
  Ideal.map ((p).stalkMap (j x)).hom
    (IdealSheafData.stalk (pullback.diagonal T.hom).ker (p (j x)))

/-- No radical is taken in the actual local kernel calculation. -/
theorem nativeExteriorParameterDiagonal_stalkMap_ker (x : Q) :
    RingHom.ker ((j).stalkMap x).hom = nativeExteriorParameterStalkIdeal X Y T z hz Z w hw x := by
  rw [ker_stalkMap_eq_idealStalk_ker, nativeExteriorParameterDiagonalInclusion_ker,
    IdealSheafData.stalk_comap]

/-- The coefficient quotient isomorphism with the literal quotient by the parameter equations. -/
def nativeExteriorParameterStalkQuotientEquiv (x : Q) :
    ((P).presheaf.stalk (j x) ⧸ nativeExteriorParameterStalkIdeal X Y T z hz Z w hw x) ≃+*
      (Q).presheaf.stalk x :=
  (Ideal.quotEquivOfEq
    (nativeExteriorParameterDiagonal_stalkMap_ker X Y T z hz Z w hw x).symm).trans
    (((j).stalkMap x).hom.quotientKerEquivOfSurjective ((j).stalkMap_surjective x))

/-- The comparison sends every quotient generator through the actual closed-immersion stalk map. -/
@[simp]
theorem nativeExteriorParameterStalkQuotientEquiv_mk (x : Q) (r : (P).presheaf.stalk (j x)) :
    dsimp% only [SmoothSite.product_hom, SmoothSite.product_left,
      Functor.const_obj_obj, Functor.id_obj]
      (nativeExteriorParameterStalkQuotientEquiv X Y T z hz Z w hw x (Ideal.Quotient.mk _ r) =
        ((j).stalkMap x).hom r) := by
  simp [nativeExteriorParameterStalkQuotientEquiv]

/-- Native flat base change of the smooth parameter diagonal is a regular immersion. -/
@[stacks 067P "Regular-immersion base change along the actual flat exterior \
  coefficient parameter pair"]
theorem nativeExteriorParameterDiagonalInclusion_regular :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion j :=
  Stacks.AlgebraicGeometry.isRegularImmersion_pullback_snd_of_flat (pullback.diagonal T.hom) p
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section (pullback.fst T.hom T.hom)
      (pullback.diagonal T.hom) (pullback.diagonal_fst T.hom))

/-- A finite regular list generates the actual parameter kernel at every quotient point. -/
theorem nativeExteriorParameterStalkIdeal_exists_regular (x : Q) :
    ∃ rs : List ((P).presheaf.stalk (j x)), IsRegular ((P).presheaf.stalk (j x)) rs ∧
      Ideal.ofList rs = nativeExteriorParameterStalkIdeal X Y T z hz Z w hw x := by
  obtain ⟨rs, hrs, hker⟩ :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
      j (nativeExteriorParameterDiagonalInclusion_regular X Y T z hz Z w hw) x
  exact ⟨rs, hrs, hker.trans (nativeExteriorParameterDiagonal_stalkMap_ker X Y T z hz Z w hw x)⟩

/-- The actual post-quotient coefficient stalk map is flat over the original coefficient stalk. -/
theorem nativeExteriorCoefficientQuotientProjection_stalkMap_flat (x : Q) :
    ((nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw).stalkMap x).hom.Flat :=
  Flat.stalkMap _ x

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/ParameterDiagonal.lean:124-136"
  "adaptation" "Regular generators of the actual native coefficient quotient kernel \
  via upstream 067P and 067R"]
  nativeExteriorParameterStalkIdeal_exists_regular

end Stacks.Chow
