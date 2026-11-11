/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceTorCycle
import Colib.AlgebraicGeometry.Correspondences.Graph.ActualTorCoefficients

/-!
# Actual graph and signed-cycle consumers of exterior Tor-cycle transport

These theorem-level consumers retain the actual incidence, native flat pullback,
and genuine graph Tor coefficient. The identity-graph generic
is constructed from the actual graph-incidence isomorphism, not supplied by a
coefficient or cycle-equality assumption.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u

namespace NativeExteriorIncidenceTorCycleTest

section ArbitraryIncidence

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "C" => fieldChowSituation k
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "π" =>
  nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "G" =>
  nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw
local notation3 (prettyPrint := false) "sI" =>
  (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom)
local notation3 (prettyPrint := false) "sI'" => (π ≫ sI)
local notation3 (prettyPrint := false) "r" => exteriorParameterDimension T
local notation3 (prettyPrint := false) "c'" =>
  incidenceTorCycle (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
    (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
    (nativeExteriorPoint Y Z T w hw) (nativeExteriorPoint_admissible Y Z T w hw)

local instance : LocallyOfFiniteType sI := by
  dsimp only [correspondenceIncidenceLeft]
  infer_instance

local instance : IsLocallyNoetherian I₀ :=
  LocallyOfFiniteType.isLocallyNoetherian (show I₀ ⟶ Spec (.of k) from sI)

example (η : genericPoints I₀) :
    geometricallyIntegralPullbackPoint π η.val = (G η).val :=
  nativeExteriorIncidence_pullbackPoint_eq_generics X Y Z T z w hz hw η

-- A negative coefficient is transported unchanged by the actual graded map.
example (η : genericPoints I₀) :
    (flatPullback C sI' sI π rfl r
      (relativeDimension_nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
      (relativeDimension (C).dimensionFunction sI η.val)
      (pointCycleAtOwnDimension C sI η.val (-3))).val = single (G η).val (-3) :=
  flatPullback_nativeExteriorIncidence_pointCycle X Y Z T z w hz hw η (-3)

example (η : genericPoints I₀) :
    (flatPullback C sI' sI π rfl r
      (relativeDimension_nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
      (relativeDimension (C).dimensionFunction sI η.val)
      (pointCycleAtOwnDimension C sI η.val 0)).val = 0 := by
  rw [flatPullback_nativeExteriorIncidence_pointCycle]
  simp

-- This is the literal product summand that the existing 02RG theorem consumes.
example (η : genericPoints I₀) :
    finiteCyclePushforward (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom
      (flatPullback C
        (exteriorIncidenceProductProjection X Y Z T z w ≫ sI) sI
        (exteriorIncidenceProductProjection X Y Z T z w) rfl r
        (relativeDimension_exteriorIncidenceProductProjection X Y Z T z w)
        (relativeDimension (C).dimensionFunction sI η.val)
        (pointCycleAtOwnDimension C sI η.val (-3))).val = single (G η).val (-3) :=
  finiteCyclePushforward_incidenceIso_flatPullback_pointCycle X Y Z T z w hz hw η (-3)

-- This checks the full actual cycle, not only its coefficients at generics.
example : c' =
    let := (finite_genericPoints_correspondenceIncidence_of_smooth
      X.hom Y.hom Z.hom z w hw).fintype
    ∑ η : genericPoints I₀,
      (flatPullback C sI' sI π rfl r
        (relativeDimension_nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
        (relativeDimension (C).dimensionFunction sI η.val)
        (pointCycleAtOwnDimension C sI η.val
          (correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η))).val :=
  incidenceTorCycle_nativeExterior_eq_sum_flatPullback X Y Z T z w hz hw

example (x : I') (hx : x ∉ genericPoints I') : c' x = 0 := by
  rw [incidenceTorCycle_nativeExterior_apply]
  exact dite_eq_right hx

example (η : genericPoints I₀) :
    c' (G η).val = correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η := by
  rw [incidenceTorCycle_apply_generic,
    correspondenceIncidenceTorCoefficient_nativeExterior]

-- Empty original generic support is allowed; no original point is manufactured.
example [IsEmpty (genericPoints I₀)] : c' = 0 := by
  rw [incidenceTorCycle_nativeExterior_eq_sum]
  simp

end ArbitraryIncidence

section IdentityGraphs

variable {k : Type u} [Field k] (X T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

private abbrev diagonalPoint (t : genericPoints X.left) : (pullback X.hom X.hom : Scheme) :=
  correspondenceGraphMap X.hom X.hom (𝟙 X.left) (Category.id_comp X.hom) t.val

private theorem diagonalPoint_admissible (t : genericPoints X.left) :
    IsFiniteCorrespondencePoint X.hom X.hom (diagonalPoint X t) :=
  isFiniteCorrespondencePoint_graphMap X.hom X.hom (𝟙 X.left)
    (Category.id_comp X.hom) t

private theorem diagonalPoint_range (t : genericPoints X.left) :
    Set.range ((integralComponentAt (diagonalPoint X t)).subschemeι ≫
      pullback.snd X.hom X.hom) ⊆ closure {t.val} := by
  dsimp only [diagonalPoint]
  have hd := integralComponentAt_graphMap_snd X.hom X.hom (𝟙 X.left)
    (Category.id_comp X.hom) t.val
  have hid := hd.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _))
  rw [hid]
  exact (range_integralComponentAt_graphMap_fst X.hom X.hom (𝟙 X.left)
    (Category.id_comp X.hom) t.val).le

/-- The actual matching graph-incidence generic, constructed from the actual isomorphism. -/
private def diagonalIncidenceGeneric (t : genericPoints X.left) :
    genericPoints (correspondenceIncidence X.hom X.hom X.hom
      (diagonalPoint X t) (diagonalPoint X t)) := by
  let := isIntegral_integralComponentAt (diagonalPoint X t)
  let e := correspondenceIncidenceGraphIso X.hom X.hom X.hom (𝟙 X.left)
    (Category.id_comp X.hom) (diagonalPoint X t) t.val (diagonalPoint_range X t)
  exact genericPointsIso e.symm
    ⟨genericPoint (integralComponentAt (diagonalPoint X t)).subscheme,
      genericPoint_mem_genericPoints _⟩

local notation3 (prettyPrint := false) "z" => diagonalPoint X
local notation3 (prettyPrint := false) "hz" => diagonalPoint_admissible X
local notation3 (prettyPrint := false) "G" =>
  fun t => nativeExteriorIncidenceGenericsEquiv X X X T (z t) (z t) (hz t) (hz t)
local notation3 (prettyPrint := false) "c'" => fun s t =>
  incidenceTorCycle (SmoothSite.product X T).hom (SmoothSite.product X T).hom
    (SmoothSite.product X T).hom (nativeExteriorPoint X X T (z s) (hz s))
    (nativeExteriorPoint X X T (z t) (hz t))
    (nativeExteriorPoint_admissible X X T (z t) (hz t))

-- The genuine coefficient is one at the constructed incidence generic.
example (t : genericPoints X.left) : c' t t (G t (diagonalIncidenceGeneric X t)).val = 1 := by
  rw [incidenceTorCycle_apply_generic,
    correspondenceIncidenceTorCoefficient_nativeExterior]
  exact correspondenceIncidenceTorCoefficient_identity_right_eq_one k X.hom X.hom
    (z t) t (diagonalIncidenceGeneric X t)

-- Signed scaling is tested on that actual graph cycle, not on a replacement model.
example (t : genericPoints X.left) :
    ((-3 : ℤ) • c' t t) (G t (diagonalIncidenceGeneric X t)).val = -3 := by
  have h : c' t t (G t (diagonalIncidenceGeneric X t)).val = 1 := by
    rw [incidenceTorCycle_apply_generic,
      correspondenceIncidenceTorCoefficient_nativeExterior]
    exact correspondenceIncidenceTorCoefficient_identity_right_eq_one k X.hom X.hom
      (z t) t (diagonalIncidenceGeneric X t)
  change (-3 : ℤ) • (c' t t (G t (diagonalIncidenceGeneric X t)).val) = -3
  rw [h]
  norm_num

-- Distinct actual diagonal components give a genuinely empty incidence contribution.
example (s t : genericPoints X.left) (hst : s ≠ t) : c' s t = 0 := by
  let hempty : IsEmpty (genericPoints
      (correspondenceIncidence X.hom X.hom X.hom (z s) (z t))) := by
    exact isEmpty_genericPoints_correspondenceIncidence_identity_right_of_ne
      k X.hom X.hom (z s) s t hst (diagonalPoint_range X s)
  dsimp only
  rw [incidenceTorCycle_nativeExterior_eq_sum X X X T (z s) (z t) (hz s) (hz t)]
  apply Finset.sum_eq_zero
  intro η _
  exact (hempty.false η).elim

end IdentityGraphs

end NativeExteriorIncidenceTorCycleTest
