/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidencePushforwardSquare
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity

/-!
# Native finite push-pull for the full exterior incidence

Let `I` be the original incidence, `q : I → X × Z` its finite outer map,
`q_T : I × T → (X × Z) × T` its base change, and `j` the common-parameter closed
immersion into `(X × T) × (Z × T)`. For every native dimension-graded cycle `α`
on `I`, Stacks 02RG and finite pushforward functoriality give

`(q_ext)_* e_* π_I^* α = j_* π_B^* q_* α`,

where `e : I × T ≅ I_ext` is the actual full-incidence isomorphism. The original
incidence is not assumed integral or reduced. Each original point can also be
inserted in its own dimension grade; the resulting coefficient identity retains
all actual residue degrees and native flat-pullback multiplicities.

The degree comparison across `e` and `j` cancels only their degree-one factors.
It does not assert that `q` or `q_T` has degree one. No field is assumed perfect,
and no residue extension is assumed separable. The identification of the actual
exterior Tor cycle with `e_* π_I^*` of the original Tor cycle is a separate
upstream theorem, not a premise or a conclusion of this module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)

local notation3 (prettyPrint := false) "C" => fieldChowSituation k
local notation3 (prettyPrint := false) "I" => correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "IT" => exteriorIncidenceProduct X Y Z T z w
local notation3 (prettyPrint := false) "BT" => exteriorOuterProduct X Z T
local notation3 (prettyPrint := false) "q" => correspondenceIncidenceMap X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "qT" => exteriorIncidenceProductOuter X Z T Y z w
local notation3 (prettyPrint := false) "πI" =>
  (pullback.fst (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom)
local notation3 (prettyPrint := false) "πB" =>
  (pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) T.hom)
local notation3 (prettyPrint := false) "sI" =>
  (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom)
local notation3 (prettyPrint := false) "sB" => (pullback.fst X.hom Z.hom ≫ X.hom)
local notation3 (prettyPrint := false) "sIT" => (πI ≫ sI)
local notation3 (prettyPrint := false) "sBT" => (πB ≫ sB)

local instance : IsIntegral T.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton
    (show T.left ⟶ Spec (.of k) from T.hom)

local instance : LocallyOfFiniteType sI := by
  dsimp only [correspondenceIncidenceLeft]
  infer_instance

/-- The dimension of the actual integral parameter over the field. -/
abbrev exteriorParameterDimension : ℕ :=
  (relativeDimension (C).dimensionFunction T.hom (genericPoint T.left)).toNat

/-- The original outer projection has the actual parameter's relative dimension. -/
theorem relativeDimension_exteriorOuterProjection :
    AlgebraicGeometry.RelativeDimension πB (exteriorParameterDimension T) :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback sB T.hom).flip
    (relativeDimension_of_isIntegral_over_field k
      (show T.left ⟶ Spec (.of k) from T.hom))

/-- The full incidence projection has the same relative dimension, without an
integrality, reducedness or flatness assumption on the original incidence. -/
theorem relativeDimension_exteriorIncidenceProductProjection :
    AlgebraicGeometry.RelativeDimension πI (exteriorParameterDimension T) :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback sI T.hom).flip
    (relativeDimension_of_isIntegral_over_field k
      (show T.left ⟶ Spec (.of k) from T.hom))

variable (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

/-- At every literal product point, the native exterior incidence map has precisely
the residue degree of the base-changed original finite map. Only the isomorphism
and the parameter-diagonal closed immersion have degree one. -/
theorem nativeExteriorIncidenceMap_residueDegree
    (p : IT) :
    (correspondenceIncidenceMap (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)).residueDegree
        ((nativeExteriorIncidenceIso X Y Z T z w hz hw).hom p) = (qT).residueDegree p := by
  have H := congrArg (fun a : IT ⟶
      pullback (SmoothSite.product X T).hom (SmoothSite.product Z T).hom =>
        a.residueDegree p)
    ((nativeExteriorIncidenceIso_hom_map X Y Z T z w hz hw).trans
      (exteriorIncidenceProductOuter_diagonal X Y Z T z w).symm)
  simpa only [residueDegree_comp, residueDegree_eq_one_of_isPreimmersion,
    one_mul, mul_one] using H

include hz hw in
/-- The native 02RG coefficient equation for one original incidence point in its
own grade. No generic-point, injectivity, reducedness or degree-one premise is used. -/
@[stacks 02RG "actual full exterior-incidence finite square, retaining every residue degree"]
theorem exteriorIncidence_fixedLabel_pushPull (x : I) (p : BT) (hp : πB p = q x) :
    let d := relativeDimension (C).dimensionFunction sI x
    let r := exteriorParameterDimension T
    ((q).residueDegree x : ℤ) * flatPullbackWeight C sBT πB (d + (r : ℤ)) p =
      ∑ᶠ a ∈ (qT).base ⁻¹' {p},
        if πI a = x then
          flatPullbackWeight C sIT πI (d + (r : ℤ)) a * ((qT).residueDegree a : ℤ)
        else 0 := by
  let := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom z w hz hw
  exact finite_flatBaseChange_fixedLabel C sI sB sIT sBT q πB πI qT
    (exteriorIncidenceProductOuter_isPullback X Z T Y z w)
    (by simp only [← Category.assoc, correspondenceIncidenceMap_fst]) rfl rfl
    (exteriorParameterDimension T) (relativeDimension_exteriorOuterProjection X Z T) x p hp

/-- Native finite pushforward commutes with the actual exterior flat pullback, followed
by the common-parameter closed immersion. This applies to any graded native cycle on
the full original incidence, independently of the still-separate Tor comparison. -/
@[stacks 02RG "actual finite incidence map and its Cartesian parameter extension",
  stacks 02R5 "finite pushforward through the full-incidence isomorphism and diagonal"]
theorem nativeExteriorIncidence_pushforward_flatPullback
    (n : ℤ) (α : CycleGroup C sI n) :
    letI := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom z w hz hw
    letI := isFinite_correspondenceIncidenceMap (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
      (nativeExteriorPoint_admissible X Y T z hz)
      (nativeExteriorPoint_admissible Y Z T w hw)
    let r := exteriorParameterDimension T
    finiteCyclePushforward
        (correspondenceIncidenceMap (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
          (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw))
        (finiteCyclePushforward (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom
          (flatPullback C sIT sI πI rfl r
            (relativeDimension_exteriorIncidenceProductProjection X Y Z T z w) n α).val) =
      finiteCyclePushforward (exteriorOuterDiagonal X Z T)
        (flatPullback C sBT sB πB rfl r
          (relativeDimension_exteriorOuterProjection X Z T) n
          (properPushforward C sI sB q
            (by simp only [← Category.assoc, correspondenceIncidenceMap_fst]) n α)).val := by
  let := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom z w hz hw
  let := isFinite_correspondenceIncidenceMap (SmoothSite.product X T).hom
    (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
    (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
    (nativeExteriorPoint_admissible X Y T z hz)
    (nativeExteriorPoint_admissible Y Z T w hw)
  let := exteriorIncidenceProductOuter_isFinite X Z T Y z w hz hw
  dsimp only
  have hmap := (nativeExteriorIncidenceIso_hom_map X Y Z T z w hz hw).trans
    (exteriorIncidenceProductOuter_diagonal X Y Z T z w).symm
  have hpush (β : AlgebraicCycle IT ℤ) :
      finiteCyclePushforward
        ((nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
          correspondenceIncidenceMap (SmoothSite.product X T).hom
            (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
            (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)) β =
        finiteCyclePushforward (qT ≫ exteriorOuterDiagonal X Z T) β := by
    simp only [finiteCyclePushforward_eq_map, hmap]
  rw [finiteCyclePushforward_comp_apply, hpush, ← finiteCyclePushforward_comp_apply]
  apply congrArg (finiteCyclePushforward (exteriorOuterDiagonal X Z T))
  exact finiteCyclePushforward_flatPullback C sI sB sIT sBT q πB πI qT
    (exteriorIncidenceProductOuter_isPullback X Z T Y z w)
    (by simp only [← Category.assoc, correspondenceIncidenceMap_fst]) rfl rfl
    (exteriorParameterDimension T) (relativeDimension_exteriorOuterProjection X Z T) n α

end Stacks.Chow
