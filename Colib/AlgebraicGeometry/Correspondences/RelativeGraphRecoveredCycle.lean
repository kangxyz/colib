/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphFiniteFactor
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphAdmissibility

/-!
# Recovering the original signed Tor incidence cycle

Push the actual Tor cycle along the proven finite factor.
Coefficients are recovered from the original incidence correspondence through
the actual closed graph. Admissibility is asserted only at surviving nonzero
coefficients, never for every incidence generic before cancellation.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)
variable (s : genericPoints V.left) (z : pullback (C := Scheme) U.hom Y.hom)
variable (hz : IsFiniteCorrespondencePoint U.hom Y.hom z)

/-- Push the unmodified signed native Tor cycle through the actual finite factor. -/
def recoveredIncidenceCycle : AlgebraicCycle (pullback (C := Scheme) V.hom Y.hom) ℤ :=
  letI := isFinite_incidenceForget k f s z hz
  finiteCyclePushforward
    (correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom
      (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s.val)
      (ambientLift k U Y z) ≫ ambientForget k)
    (incidenceTorCycle V.hom U.hom (SmoothSite.product U Y).hom
      (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s.val)
      (ambientLift k U Y z) (image_admissible k U Y z hz))

/-- Reinsert the retained coordinate to recover the original incidence value. -/
theorem recoveredIncidenceCycle_push :
    finiteCyclePushforward (ambientOver k (Y := Y) f) (recoveredIncidenceCycle k f s z hz) =
      (incidenceTorCorrespondence V.hom U.hom (SmoothSite.product U Y).hom
        (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s.val)
        (ambientLift k U Y z)
        (isFiniteCorrespondencePoint_graphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
        (image_admissible k U Y z hz)).val := by
  let := isFinite_incidenceForget k f s z hz
  let := isFinite_correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom
    (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s.val)
    (ambientLift k U Y z)
    (isFiniteCorrespondencePoint_graphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
    (image_admissible k U Y z hz)
  rw [recoveredIncidenceCycle, finiteCyclePushforward_comp_apply,
    incidenceTorCorrespondence_val]
  exact DFunLike.congr_fun (AlgebraicCycle.finiteCyclePushforward_congr _ _
    (incidenceMap_factor_over k f s.val z)) _

/-- Each recovered signed coefficient is literally the original coefficient on
its closed image, after all collisions and cancellation. -/
theorem recoveredIncidenceCycle_apply (x : pullback (C := Scheme) V.hom Y.hom) :
    recoveredIncidenceCycle k f s z hz x =
      (incidenceTorCorrespondence V.hom U.hom (SmoothSite.product U Y).hom
        (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s.val)
        (ambientLift k U Y z)
        (isFiniteCorrespondencePoint_graphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
        (image_admissible k U Y z hz)).val (ambientOver k f x) := by
  rw [← recoveredIncidenceCycle_push]
  exact (finiteCyclePushforward_apply_of_isClosedImmersion
    (ambientOver k (Y := Y) f) (recoveredIncidenceCycle k f s z hz) x).symm

/-- Only surviving nonzero coefficients need admissibility; reflect the original
native incidence correspondence's admissibility through the closed graph. -/
theorem recoveredIncidenceCycle_admissible
    (x : pullback (C := Scheme) V.hom Y.hom)
    (hx : recoveredIncidenceCycle k f s z hz x ≠ 0) :
    IsFiniteCorrespondencePoint V.hom Y.hom x := by
  apply admissible_of_ambientOver k f x
  exact isFiniteCorrespondencePoint_of_incidenceTorCorrespondence_ne_zero
    V.hom U.hom (SmoothSite.product U Y).hom _ _
    (isFiniteCorrespondencePoint_graphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
    (image_admissible k U Y z hz) _
    (by simpa only [recoveredIncidenceCycle_apply] using hx)

/-- The finite factor sends the finite native Tor support to a finite support. -/
theorem recoveredIncidenceCycle_finite_support :
    (recoveredIncidenceCycle k f s z hz).support.Finite := by
  let := isFinite_incidenceForget k f s z hz
  exact finiteCyclePushforward_finite_support _ _
    (finite_support_incidenceTorCycle V.hom U.hom (SmoothSite.product U Y).hom _ _
      (image_admissible k U Y z hz))

/-- The recovered original Tor cycle is a genuine finite correspondence. -/
def recoveredIncidenceCorrespondence : Cor.mk V ⟶ Cor.mk Y :=
  ⟨recoveredIncidenceCycle k f s z hz,
    recoveredIncidenceCycle_finite_support k f s z hz,
    recoveredIncidenceCycle_admissible k f s z hz⟩

end AlgebraicGeometry.Cor.RelativeGraph
