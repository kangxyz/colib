/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.GeometricallyIntegralPullback
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidencePushPull
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceTorCoefficients

/-!
# Actual exterior incidence Tor cycles in their pointwise grades

For the actual parameter-forgetting map pi, the generic of the inverse image of
an original prime closure is the point selected by the existing generic-point
equivalence G. This follows from the support of the scheme-theoretic inverse
image and the existing closure formula for G, not from an equality of cycles.

Reindex the existing incidenceTorCycle by G and substitute the existing literal
Tor coefficient comparison. Each original generic eta is pulled back in its own
relative-dimension grade. No common grade for the incidence is assumed. The full
incidence is not reduced: only integralComponentAt eta, the reduced prime closure
that defines a native point cycle, enters the prime-pullback calculation.

The second cycle formula uses the actual full-incidence isomorphism and the
literal product projection, so each summand is an input to the existing native
02RG theorem. It does not reprove push-pull, identify the target exterior cycle,
or assert exterior compatibility of composition. Integer signs, zero coefficients,
and zero away from the generic support are retained.

Inputs: Colib e7697ab8164435c7093665d02ac34f021eefb75e,
Composition/TorCycle.lean:83-109 and Chow/FinitePushforward.lean:175-181;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:73-77;
Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
StacksFrontier/AlgebraicGeometry/Chow/GysinConstruction/IntegralComponent.lean:187-205,269-296.
The imported full-incidence isomorphism adapts Motivic
a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Incidence.lean:258-279.
This is attribution of the actual geometric input, not of the present Tor-cycle
comparison. The point-pullback, generic-point, and Tor comparisons are used through
the four explicit lower imports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "C" => fieldChowSituation k
local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "z'" => nativeExteriorPoint X Y T z hz
local notation3 (prettyPrint := false) "w'" => nativeExteriorPoint Y Z T w hw
local notation3 (prettyPrint := false) "hw'" => nativeExteriorPoint_admissible Y Z T w hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "π" =>
  nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "G" =>
  nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw
local notation3 (prettyPrint := false) "IT" => exteriorIncidenceProduct X Y Z T z w
local notation3 (prettyPrint := false) "πI" => exteriorIncidenceProductProjection X Y Z T z w
local notation3 (prettyPrint := false) "GI" =>
  exteriorIncidenceProductGenericsEquiv X Y Z T z w
local notation3 (prettyPrint := false) "e" => nativeExteriorIncidenceIso X Y Z T z w hz hw
local notation3 (prettyPrint := false) "sI" =>
  (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom)
local notation3 (prettyPrint := false) "sI'" => (π ≫ sI)
local notation3 (prettyPrint := false) "sIT" => (πI ≫ sI)
local notation3 (prettyPrint := false) "r" => exteriorParameterDimension T

local instance : LocallyOfFiniteType sI := by
  dsimp only [correspondenceIncidenceLeft]
  infer_instance

local instance : IsLocallyNoetherian I₀ :=
  LocallyOfFiniteType.isLocallyNoetherian (show I₀ ⟶ Spec (.of k) from sI)

/-- The actual inverse-image generic is the existing native exterior generic label. -/
theorem nativeExteriorIncidence_pullbackPoint_eq_generics
    (η : genericPoints I₀) :
    geometricallyIntegralPullbackPoint π η.val = (G η).val := by
  have h : IsGenericPoint (geometricallyIntegralPullbackPoint π η.val)
      (closure ({(G η).val} : Set I')) := by
    change closure ({(genericPointOf ((integralComponentAt η.val).comap π)
      (isIntegral_comap_integralComponentAt π η.val))} : Set I') = _
    rw [← support_eq_closure_genericPointOf, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, coe_support_integralComponentAt,
      nativeExteriorIncidenceGenericsEquiv_closure]
  exact h.eq isGenericPoint_closure

/-- The actual native incidence projection has the existing parameter grade. -/
theorem relativeDimension_nativeExteriorIncidenceOriginal :
    AlgebraicGeometry.RelativeDimension π r := by
  let : IsIntegral T.left := GeometricallyIntegral.isIntegral_of_subsingleton
    (show T.left ⟶ Spec (.of k) from T.hom)
  exact AlgebraicGeometry.RelativeDimension.of_isPullback
    (nativeExteriorIncidenceOriginal_isPullback X Y Z T z w hz hw).flip
    (relativeDimension_of_isIntegral_over_field k
      (show T.left ⟶ Spec (.of k) from T.hom))

/-- Native pullback at the original point's own grade, with any signed coefficient. -/
@[stacks 02RB "pointwise application of the native flat pullback to an original incidence prime"]
theorem flatPullback_nativeExteriorIncidence_pointCycle
    (η : genericPoints I₀) (n : ℤ) :
    (flatPullback C sI' sI π rfl r
      (relativeDimension_nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
      (relativeDimension (C).dimensionFunction sI η.val)
      (pointCycleAtOwnDimension C sI η.val n)).val = single (G η).val n := by
  rw [flatPullback_pointCycleAtOwnDimension,
    nativeExteriorIncidence_pullbackPoint_eq_generics]

/-- The same support calculation identifies the literal product's generic label. -/
theorem exteriorIncidenceProduct_pullbackPoint_eq_generics
    (η : genericPoints I₀) :
    geometricallyIntegralPullbackPoint πI η.val = (GI η).val := by
  have h : IsGenericPoint (geometricallyIntegralPullbackPoint πI η.val)
      (closure ({(GI η).val} : Set IT)) := by
    change closure ({(genericPointOf ((integralComponentAt η.val).comap πI)
      (isIntegral_comap_integralComponentAt πI η.val))} : Set IT) = _
    rw [← support_eq_closure_genericPointOf, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, coe_support_integralComponentAt,
      exteriorIncidenceProductGenericsEquiv_closure]
  exact h.eq isGenericPoint_closure

/-- Transport through the actual full-incidence isomorphism preserves the signed
point coefficient. Degree one is used only for this isomorphism, not for pi. -/
theorem finiteCyclePushforward_incidenceIso_flatPullback_pointCycle
    (η : genericPoints I₀) (n : ℤ) :
    finiteCyclePushforward (e).hom
      (flatPullback C sIT sI πI rfl r
        (relativeDimension_exteriorIncidenceProductProjection X Y Z T z w)
        (relativeDimension (C).dimensionFunction sI η.val)
        (pointCycleAtOwnDimension C sI η.val n)).val = single (G η).val n := by
  rw [flatPullback_pointCycleAtOwnDimension,
    exteriorIncidenceProduct_pullbackPoint_eq_generics,
    finiteCyclePushforward_single_of_isClosedImmersion]
  have hpoint : (e).hom (GI η).val = (G η).val := by
    rw [← nativeExteriorIncidenceIso_inv_generics X Y Z T z w hz hw η]
    simp
  rw [hpoint]

/-- Reindex the existing actual Tor cycle by the actual generic-point equivalence.
The coefficient remains the original signed alternating Tor length. -/
theorem incidenceTorCycle_nativeExterior_eq_sum :
    incidenceTorCycle fX fY fZ z' w' hw' =
      let := (finite_genericPoints_correspondenceIncidence_of_smooth
        X.hom Y.hom Z.hom z w hw).fintype
      ∑ η : genericPoints I₀,
        single (G η).val (correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η) := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth
    X.hom Y.hom Z.hom z w hw).fintype
  let := (finite_genericPoints_correspondenceIncidence_of_smooth fX fY fZ z' w' hw').fintype
  rw [incidenceTorCycle_eq_sum]
  calc
    (∑ ξ : genericPoints I',
        single ξ.val (correspondenceIncidenceTorCoefficient k fX fY fZ z' w' ξ)) =
        ∑ η : genericPoints I₀,
          single (G η).val (correspondenceIncidenceTorCoefficient k fX fY fZ z' w' (G η)) :=
      ((G).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro η hη
      rw [correspondenceIncidenceTorCoefficient_nativeExterior]

/-- The actual exterior Tor cycle is the finite sum of actual flat pullbacks,
with the dimension grade chosen separately for each original generic point. -/
theorem incidenceTorCycle_nativeExterior_eq_sum_flatPullback :
    incidenceTorCycle fX fY fZ z' w' hw' =
      let := (finite_genericPoints_correspondenceIncidence_of_smooth
        X.hom Y.hom Z.hom z w hw).fintype
      ∑ η : genericPoints I₀,
        (flatPullback C sI' sI π rfl r
          (relativeDimension_nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
          (relativeDimension (C).dimensionFunction sI η.val)
          (pointCycleAtOwnDimension C sI η.val
            (correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η))).val := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth
    X.hom Y.hom Z.hom z w hw).fintype
  rw [incidenceTorCycle_nativeExterior_eq_sum]
  apply Finset.sum_congr rfl
  intro η hη
  exact (flatPullback_nativeExteriorIncidence_pointCycle X Y Z T z w hz hw η _).symm

/-- The literal product form exposes precisely the summands consumed by the
existing native finite push-pull theorem. No common incidence grade is imposed. -/
theorem incidenceTorCycle_nativeExterior_eq_sum_incidenceIso_flatPullback :
    incidenceTorCycle fX fY fZ z' w' hw' =
      let := (finite_genericPoints_correspondenceIncidence_of_smooth
        X.hom Y.hom Z.hom z w hw).fintype
      ∑ η : genericPoints I₀,
        finiteCyclePushforward (e).hom
          (flatPullback C sIT sI πI rfl r
            (relativeDimension_exteriorIncidenceProductProjection X Y Z T z w)
            (relativeDimension (C).dimensionFunction sI η.val)
            (pointCycleAtOwnDimension C sI η.val
              (correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η))).val := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth
    X.hom Y.hom Z.hom z w hw).fintype
  rw [incidenceTorCycle_nativeExterior_eq_sum]
  apply Finset.sum_congr rfl
  intro η hη
  exact (finiteCyclePushforward_incidenceIso_flatPullback_pointCycle
    X Y Z T z w hz hw η _).symm

/-- Evaluation retains zero at every nongeneric point, not just the generic formula. -/
theorem incidenceTorCycle_nativeExterior_apply (x : I') :
    incidenceTorCycle fX fY fZ z' w' hw' x =
      if hx : x ∈ genericPoints I' then
        correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w
          ((G).symm ⟨x, hx⟩)
      else 0 := by
  classical
  split_ifs with hx
  · rw [incidenceTorCycle_apply_generic fX fY fZ z' w' hw' ⟨x, hx⟩]
    simpa only [Equiv.apply_symm_apply] using
      correspondenceIncidenceTorCoefficient_nativeExterior X Y Z T z w hz hw
        ((G).symm ⟨x, hx⟩)
  · exact incidenceTorCycle_apply_of_notMem fX fY fZ z' w' hw' x hx

end Stacks.Chow
