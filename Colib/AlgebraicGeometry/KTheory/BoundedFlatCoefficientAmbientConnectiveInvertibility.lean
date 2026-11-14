/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientInverseOperation

/-! # Connective invertibility of the original ambient Bass seed -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients AlgebraicGeometry.Scheme.ProjectiveLine
open CommRingCat.PolynomialLaurent Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.TwoChartStable

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  [CompactSpace P.left] (a : Under R)

local notation "A" => (boundedAboveFlatCoefficientAmbientLaurentAction P)
local notation "S" => (coefficientConnectiveSquare P a)
local notation "X" => (compactFiber P a)
local notation "l" => (coefficientLaurentObject a)
local notation "E" n => (boundedAboveFlatCoefficientAmbientBassConnectiveNatIso P n)

attribute [local instance] Waldhausen.Additivity.KCommGroup

set_option maxHeartbeats 700000 in
-- The original Laurent K comparison simultaneously unfolds both chosen spectrum evaluations.
/-- The actual geometric inverse operation represents the inverse fine scalar on the same
original Laurent coefficient class. -/
theorem coefficientAmbientInverseOperation_comparison (n : ℕ) :
    AddCommGrpCat.ofHom (positiveBassUnitSection X n).toAdditive ≫
        (coefficientConnectiveLaurentIso P a (n + 1)).hom =
      (E n).hom.app a ≫ ((A).symm.track.homotopy a).stableOperation (n : ℤ) := by
  let L := boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, l)
  let D := stableHomotopyFunctor (((n + 1 : ℕ) : ℤ))
  have hL : IsIso (D.map L) :=
    boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_isStableEquivalence
      (op P, l) _
  apply (cancel_mono (D.map L)).mp
  have e := boundedAboveFlatCoefficientAmbientBassConnectiveNatIso_evaluation P (n + 1) l
  have eo := boundedAboveFlatCoefficientAmbientBassConnectiveNatIso_evaluation P n a
  have hu := coefficientAmbientInverseScalar_evaluation P a (n : ℤ)
  change ((A).symm.track.homotopy a).stableOperation (n : ℤ) ≫ D.map L = _ at hu
  simp only [coefficientConnectiveLaurentIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  change ((E (n + 1)).app l).hom ≫ D.map L = _ at e
  rw [e, hu, ← Category.assoc ((E n).hom.app a), eo]
  apply AddCommGrpCat.ext
  intro x
  have h := DFunLike.congr_fun (positiveBassUnitSection_coefficient P a n) x.toMul
  let C := (perfectComplexesWaldhausen (space (op P, l)).toRingedSpace)
  let B := (perfectComplexesWaldhausen (space (op P, a)).toRingedSpace)
  change originalKStableEquiv C (n + 1) (Additive.ofMul
    (perfectKPullback (compactFiberLaurentIso P a).hom (n + 1)
      (positiveBassUnitSection X n x.toMul))) =
    (perfectFlatUnitHomotopy
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.laurentProjection P a)
      (coefficientLaurentScalar P a)⁻¹).stableOperation (n : ℤ)
        (originalKStableEquiv B n (Additive.ofMul x.toMul))
  rw [perfectKPullback_eq_flatPullback]
  refine (congrArg (fun t => originalKStableEquiv C (n + 1) (Additive.ofMul t)) h).trans ?_
  exact originalKSelfTrackOperation_stable _ _ _ n x.toMul

variable [QuasiSeparatedSpace P.left]

set_option maxHeartbeats 600000 in
-- The two literal cokernels have large original spectral source and target types.
/-- The original inverse fine scalar induces an isomorphism onto the actual Laurent cokernel. -/
theorem coefficientAmbientInverseUnitQuotient_isIso (n : ℕ) :
    IsIso (((A).symm.track.stableUnitQuotient (n : ℤ)).app a) := by
  let : QuasiSeparatedSpace (X).obj := quasiSeparatedSpace_space (op P, a)
  let e := (E n).app a
  let c := coefficientConnectiveCokernelIso P a (n + 1)
  have he : positiveBassInverseQuotientHom X n ≫ c.hom =
      e.hom ≫ ((A).symm.track.stableUnitQuotient (n : ℤ)).app a := by
    rw [LaurentSeed.Track.stableUnitQuotient_app]
    change (AddCommGrpCat.ofHom (positiveBassUnitSection X n).toAdditive ≫
      cokernel.π (positiveBassDifferenceHom X (n + 1))) ≫ c.hom = _
    rw [Category.assoc, coefficientConnectiveCokernelIso_π, ← Category.assoc,
      coefficientAmbientInverseOperation_comparison, Category.assoc]
    rfl
  let k := ((A).symm.track.stableUnitQuotient (n : ℤ)).app a
  let j := positiveBassInverseQuotientHom X n
  have hj : IsIso (j ≫ c.hom) := by
    dsimp only [j]
    infer_instance
  have hk : IsIso (e.hom ≫ k) :=
    Eq.mp (congrArg (fun f => IsIso f) he) hj
  let : IsIso (e.hom ≫ k) := hk
  exact IsIso.of_isIso_comp_left e.hom k

/-- The unchanged ambient strict seed is invertible in every connective degree. -/
instance boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientAmbientBassTransition P 0).app a)) := by
  let : IsIso (((A).symm.track.stableUnitQuotient (n : ℤ)).app a) :=
    coefficientAmbientInverseUnitQuotient_isIso P a n
  have h := NatTrans.congr_app ((A).symm_stableUnitQuotient (n : ℤ)) a
  change ((A).symm.track.stableUnitQuotient (n : ℤ)).app a =
    -((A).track.stableUnitQuotient (n : ℤ)).app a at h
  let : IsIso (((A).track.stableUnitQuotient (n : ℤ)).app a) := by
    rw [← neg_neg (((A).track.stableUnitQuotient (n : ℤ)).app a), ← h]
    change IsIso (-(asIso (((A).symm.track.stableUnitQuotient (n : ℤ)).app a))).hom
    infer_instance
  exact (A).track.seed_isIso_of_chart_exact_of_stableUnitQuotient a
    (boundedAboveFlatCoefficientAmbientTwoChartSpectralConditions P 0 a) (n : ℤ)
    ((ShortComplex.ab_exact_iff_function_exact _).mp (coefficientConnectiveChart_exact P a n))

end AlgebraicGeometry.Scheme.Modules
