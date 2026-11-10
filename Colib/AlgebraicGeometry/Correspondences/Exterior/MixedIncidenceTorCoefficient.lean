/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedComponentSelection
public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceHigherTor
public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceTorZero

/-!
# The actual matched mixed Tor coefficient and cycle

The unique matching graph component is selected by its actual source range.
At its actual generic incidence point, the native finite alternating integer
Tor sum is one: the previously constructed common regular list kills every
positive degree, and the actual ambient-linear degree-zero identification
computes length one. No Tor or coefficient hypothesis is introduced.

The actual incidence is integral through the actual support isomorphisms.
Consequently its native Tor cycle is its single generic prime with coefficient
one. The integer signs in the defining sum are evaluated, not discarded.

Stacks 0AZT records Tor coherence, stalks, support and boundedness. The
alternating-length convention is in the unnumbered paragraph after that lemma
in section 43.14 (0AZR), whose chapter assumes an algebraically closed field
(0AZ8). These are background conventions only: the arbitrary-field result
here follows from the actual native module and smooth-geometry proofs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "t" => nativeMixedMatchingComponent X Y T z hz
local notation3 (prettyPrint := false) "a" => nativeParameterGraphPoint X T U ψ t
local notation3 (prettyPrint := false) "b" => nativeExteriorPoint X Y U z hz

/-- The selected actual mixed incidence is integral, with no assumed support identification. -/
theorem isIntegral_nativeMixedMatchingIncidence :
    IsIntegral (nativeMixedGraphIncidence X Y T U ψ z hz t) := by
  let e := (nativeExteriorSupportIso X Y T z hz).symm ≪≫
    nativeMixedMatchingComponentIncidenceIso X Y T z hz U ψ
  exact IsIntegral.of_isIso e.hom

/-- The literal finite alternating integer Tor sum on the selected incidence is one. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeStalks.lean:196-237"
  "adaptation" "Application of the actual common regular list and degree-zero \
    ambient-module identification to the native integer Tor sum",
  stacks 0AZT "background only: coherence, stalks, support and boundedness of Tor; the \
    arbitrary-field native calculation is proved here",
  stacks 0AZR "background only: section43.14 unnumbered Tor-length formula after \
    Lemma43.14.2, under the chapter43 algebraically closed convention; not an \
    arbitrary-field theorem input"]
theorem nativeMixedMatchingIncidenceTorCoefficient_eq_one
    (x : genericPoints (nativeMixedGraphIncidence X Y T U ψ z hz t)) :
    correspondenceIncidenceTorCoefficient k f g h a b x = 1 := by
  rw [correspondenceIncidenceTorCoefficient_eq_sum]
  rw [Finset.sum_eq_single 0]
  · rw [length_nativeMixedGraphIncidenceAmbientTor_zero_eq_one X Y T U ψ z hz t
      (nativeMixedMatchingComponent_range_subset X Y T z hz U ψ) x.val
      ((mem_genericPoints_iff_isMax _ _).mp x.property)]
    simp
  · intro n hn hn0
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ n =>
      have hlen := (Module.length_eq_zero_iff
        (R := correspondenceIncidenceAmbientStalk f g h a b x.val)).mpr
        (ModuleCat.isZero_iff_subsingleton.mp
          (isZero_nativeMixedIncidenceAmbientTor_succ X Y T U ψ z hz t x.val n))
      simp only [hlen, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim

open Classical in
/-- The full native Tor cycle is the single generic prime of the actual matched incidence. -/
theorem nativeMixedMatchingIncidenceTorCycle_eq_single :
    letI := isIntegral_nativeMixedMatchingIncidence X Y T U ψ z hz
    incidenceTorCycle f g h a b (nativeExteriorPoint_admissible X Y U z hz) =
      single (genericPoint (nativeMixedGraphIncidence X Y T U ψ z hz t)) 1 := by
  classical
  let := isIntegral_nativeMixedMatchingIncidence X Y T U ψ z hz
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints (nativeMixedGraphIncidence X Y T U ψ z hz t)
  · have hx' : x = genericPoint (nativeMixedGraphIncidence X Y T U ψ z hz t) := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
    rw [← hx', single_apply, ite_eq_left rfl]
    exact (incidenceTorCycle_apply_generic f g h a b
      (nativeExteriorPoint_admissible X Y U z hz) ⟨x, hx⟩).trans
      (nativeMixedMatchingIncidenceTorCoefficient_eq_one X Y T U ψ z hz ⟨x, hx⟩)
  · have hx' : x ≠ genericPoint (nativeMixedGraphIncidence X Y T U ψ z hz t) := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
    rw [incidenceTorCycle_apply_of_notMem f g h a b
      (nativeExteriorPoint_admissible X Y U z hz) x hx, single_apply]
    simp only [hx', ite_false]

end Stacks.Chow
