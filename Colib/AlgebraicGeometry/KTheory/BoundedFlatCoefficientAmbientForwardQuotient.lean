/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientConnectiveInvertibility

/-! # The signed forward unit in the actual coefficient Bass quotient -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients AlgebraicGeometry.Scheme.ProjectiveLine
open CommRingCat.PolynomialLaurent Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.TwoChartStable

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Waldhausen.Additivity.KCommGroup

set_option maxHeartbeats 620000 in
-- Keep the genuine geometric boundary, not merely an inverse on abstract quotients.
/-- The additive cokernel comparison is the actual first-coordinate boundary on representatives. -/
theorem positiveBassAdditiveCokernelBoundary_π
    (X : Scheme.QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ) :
    cokernel.π (positiveBassDifferenceHom X (n + 1)) ≫
        (asIso (positiveBassInverseQuotientHom X n)).inv =
      AddCommGrpCat.ofHom (positiveBassBoundary X n).toAdditive := by
  let f := positiveBassDifferenceHom X (n + 1)
  let g := AddCommGrpCat.ofHom (positiveBassBoundary X n).toAdditive
  have hf : f ≫ g = 0 := by
    apply AddCommGrpCat.ext
    intro x
    change Additive.ofMul (positiveBassBoundary X n (relativeLaurentDifference X (n + 1) x.toMul))
      = Additive.ofMul 1
    apply congrArg Additive.ofMul
    have h : relativeLaurentDifference X (n + 1) x.toMul ∈ (positiveBassBoundary X n).ker := by
      rw [← relativeLaurentDifference_range_eq_ker X n]
      exact ⟨x.toMul, rfl⟩
    exact h
  have hsection : positiveBassInverseQuotientHom X n ≫ cokernel.desc f g hf = 𝟙 _ := by
    change (AddCommGrpCat.ofHom (positiveBassUnitSection X n).toAdditive ≫ cokernel.π f) ≫
      cokernel.desc f g hf = _
    rw [Category.assoc, cokernel.π_desc]
    apply AddCommGrpCat.ext
    intro x
    exact congrArg Additive.ofMul (DFunLike.congr_fun (positiveBassBoundary_comp_unitSection X n)
      x.toMul)
  have hdesc : cokernel.desc f g hf = (asIso (positiveBassInverseQuotientHom X n)).inv := by
    apply (cancel_epi (asIso (positiveBassInverseQuotientHom X n)).hom).mp
    rw [Iso.hom_inv_id]
    exact hsection
  rw [← hdesc]
  exact cokernel.π_desc f g hf

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  [CompactSpace P.left] [QuasiSeparatedSpace P.left] (a : Under R)

local notation "A" => (boundedAboveFlatCoefficientAmbientLaurentAction P)
local notation "Xₐ" => (compactFiber P a)
local notation "E" n => (boundedAboveFlatCoefficientAmbientBassConnectiveNatIso P n)

set_option maxHeartbeats 600000 in
-- Both original coefficient spectra underlie the two literal cokernels.
/-- The actual inverse coefficient operation is the geometric inverse section under the
literal comparison of Laurent quotients. -/
theorem coefficientAmbientInverseUnitQuotient_comparison (n : ℕ) :
    positiveBassInverseQuotientHom Xₐ n ≫ (coefficientConnectiveCokernelIso P a (n + 1)).hom =
      (E n).hom.app a ≫ ((A).symm.track.stableUnitQuotient (n : ℤ)).app a := by
  rw [LaurentSeed.Track.stableUnitQuotient_app]
  change (AddCommGrpCat.ofHom (positiveBassUnitSection Xₐ n).toAdditive ≫
    cokernel.π (positiveBassDifferenceHom Xₐ (n + 1))) ≫
    (coefficientConnectiveCokernelIso P a (n + 1)).hom = _
  rw [Category.assoc, coefficientConnectiveCokernelIso_π, ← Category.assoc,
    coefficientAmbientInverseOperation_comparison, Category.assoc]
  rfl

set_option maxHeartbeats 600000 in
-- The coefficient and geometric cokernels retain their original stable chosen-zero groups.
/-- The original geometric boundary, transported to the actual additive coefficient quotient. -/
def coefficientAmbientPositiveBassBoundaryIso (n : ℕ) :=
  let : QuasiSeparatedSpace (Xₐ).obj := quasiSeparatedSpace_space (op P, a)
  (coefficientConnectiveCokernelIso P a (n + 1)).symm ≪≫
    (asIso (positiveBassInverseQuotientHom Xₐ n)).symm ≪≫ (E n).app a

set_option maxHeartbeats 600000 in
-- The representative is transported through the same two selected cokernels.
/-- The transported coefficient boundary agrees with the actual geometric boundary on the
original Laurent representatives. -/
theorem coefficientAmbientPositiveBassBoundaryIso_π (n : ℕ) :
    letI : QuasiSeparatedSpace (Xₐ).obj := quasiSeparatedSpace_space (op P, a)
    (coefficientConnectiveLaurentIso P a (n + 1)).hom ≫
      cokernel.π (chartDifference (coefficientConnectiveSquare P a) ((n + 1 : ℕ) : ℤ)) ≫
      (coefficientAmbientPositiveBassBoundaryIso P a n).hom =
    AddCommGrpCat.ofHom (positiveBassBoundary Xₐ n).toAdditive ≫ (E n).hom.app a := by
  let : QuasiSeparatedSpace (Xₐ).obj := quasiSeparatedSpace_space (op P, a)
  rw [← Category.assoc, ← coefficientConnectiveCokernelIso_π, Category.assoc]
  simp only [coefficientAmbientPositiveBassBoundaryIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, positiveBassAdditiveCokernelBoundary_π]
  rfl

set_option maxHeartbeats 600000 in
-- Elaboration unfolds the comparisons of the coefficient and geometric cokernels.
/-- The forward Laurent operation in the actual quotient is the negative of the inverse
geometric boundary. -/
@[colib_tag "COL-1291", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassForwardQuotient.lean:56-63"
  "adaptation" "The literal forward scalar into the additive coefficient quotient"]
theorem coefficientAmbientForwardUnitQuotient_eq_neg_inv (n : ℕ) :
    ((A).track.stableUnitQuotient (n : ℤ)).app a =
      -(coefficientAmbientPositiveBassBoundaryIso P a n).inv := by
  have h := NatTrans.congr_app ((A).symm_stableUnitQuotient (n : ℤ)) a
  change ((A).symm.track.stableUnitQuotient (n : ℤ)).app a =
    -((A).track.stableUnitQuotient (n : ℤ)).app a at h
  rw [← neg_neg (((A).track.stableUnitQuotient (n : ℤ)).app a), ← h]
  congr 1
  apply (cancel_epi ((E n).hom.app a)).mp
  rw [← coefficientAmbientInverseUnitQuotient_comparison]
  simp [coefficientAmbientPositiveBassBoundaryIso, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
