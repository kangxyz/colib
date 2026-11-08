/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.DualInverseImage
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.JointRetarget
public import Colib.KTheory.Waldhausen.Approximation.Dual

/-! # Dual approximation with genuine inverse-image weak classes

The same fine factorization supplies the relative factorization. Coarse joint
exactness is derived from the original fine joint data and saturation.

Implementation provenance: `Quillen/Waldhausen/Approximation/DualInverseImage.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual maps, structural hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  {U : Structure E} {Ud : Structure Eᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd)
  (hU : IsCompatibleDual U Ud) {F : C ⥤ D} {G : D ⥤ E}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (hG : IsExact V.cof V.weq U.cof U.weq G)
  (hGd : IsExact Vd.cof Vd.weq Ud.cof Ud.weq G.op)
  (h : HasDualApproximationProperty W V Wd.cof.unop F)

include hW hV hU hFd hGd h in
/-- Actual relative K-equivalence from fine incoming factorizations and fine joint data. -/
theorem KMap_bijective_of_dualApproximation_inverseImage
    [U.weq.HasTwoOutOfThreeProperty]
    (Jd : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
    (n : ℕ) : Function.Bijective (KMap (inverseImageComposite_exact hF hG) n) := by
  let := hU.dual_saturated
  let : (Structure.inverseImageWeakNested (hFd.comp hGd)).coarse.weq.HasTwoOutOfThreeProperty :=
    Structure.withInverseImageWeak_twoOutOfThree (hFd.comp hGd)
  exact KMap_bijective_of_dualApproximation
    (hW.withInverseImageWeak hU (hF.comp hG) (hFd.comp hGd))
    (hV.withInverseImageWeak hU hG hGd)
    (inverseImageComposite_exact hF hG) (inverseImageComposite_exact hFd hGd)
    (h.inverseImageComposite hF hG)
    (Jd.toCoarse (Structure.inverseImageWeakNested (hFd.comp hGd))) n

end CategoryTheory.Waldhausen
