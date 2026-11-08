/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.DualInverseImageLift
public import Colib.KTheory.Waldhausen.Approximation.DualInverseImage

/-! # Inverse-image dual approximation from genuine fine lifts alone

Reflection of the coarse weak class is definitional. Fine weak reflection is
neither required nor asserted; in particular, open restriction may annihilate
nontrivial global supported complexes. The strict original incoming equations
and actual source joint data are retained.

Implementation provenance: `Quillen/Waldhausen/Approximation/DualInverseImageLift.lean`
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
  (hlift : ∀ {X : C} {Y : D} (f : Y ⟶ F.obj X),
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      Wd.cof.unop i ∧ V.weq p ∧ p ≫ F.map i = f)

include hW hV hU hFd hGd hlift in
/-- Coarse dual approximation retains the original functor K-map, with no
fine reflection or homotopy-cartesian premise. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Approximation/DualInverseImageLift.lean:49-64"
    "adaptation"
    "Inverse-image KMap bijectivity from strict fine incoming lifts without fine reflection"]
theorem KMap_bijective_of_dualLift_inverseImage
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
    (dualApproximation_of_inverseImageLift hF hG hlift)
    (Jd.toCoarse (Structure.inverseImageWeakNested (hFd.comp hGd))) n

end CategoryTheory.Waldhausen
