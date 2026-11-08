/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.DualInverseImage

/-! # Inverse-image dual approximation from genuine fine lifts alone

Reflection of the coarse weak class is definitional. Fine weak reflection is
neither required nor asserted; in particular, open restriction may annihilate
nontrivial global supported complexes. The strict original incoming equations
are retained without any K-theoretic hypothesis.

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

include hlift in
/-- The actual inverse-image class supplies reflection; only fine incoming
factorization is needed to obtain genuine coarse dual App1/App2. -/
theorem dualApproximation_of_inverseImageLift :
    HasDualApproximationProperty (Structure.withInverseImageWeak (hF.comp hG))
      (Structure.withInverseImageWeak hG) Wd.cof.unop F where
  reflects _ hf := hf
  lift f := by
    obtain ⟨X', i, p, hi, hp, he⟩ := hlift f
    exact ⟨X', i, p, hi, hG.weak p hp, he⟩

end CategoryTheory.Waldhausen
