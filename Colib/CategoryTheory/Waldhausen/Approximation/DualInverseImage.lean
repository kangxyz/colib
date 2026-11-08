/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Duality.InverseImageWeak
public import Colib.CategoryTheory.Waldhausen.Approximation.Dual

/-! # Dual approximation for genuine inverse-image weak classes

The unchanged exact functor and strict fine incoming factorizations supply
approximation for the relative weak classes. No K-theoretic hypothesis is used.

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

/-- Exactness for inverse-image weak classes uses the unchanged original map. -/
theorem inverseImageComposite_exact :
    IsExact (Structure.withInverseImageWeak (hF.comp hG)).cof
      (Structure.withInverseImageWeak (hF.comp hG)).weq
      (Structure.withInverseImageWeak hG).cof (Structure.withInverseImageWeak hG).weq F where
  zero := hF.zero
  cofibration := hF.cofibration
  weak _ hf := hf
  pushout := hF.pushout

include h in
/-- Reuse the original fine lift, including its literal factorization equation. -/
theorem HasDualApproximationProperty.inverseImageComposite :
    HasDualApproximationProperty (Structure.withInverseImageWeak (hF.comp hG))
      (Structure.withInverseImageWeak hG) Wd.cof.unop F where
  reflects _ hf := hf
  lift f := by
    obtain ⟨X, i, p, hi, hp, he⟩ := h.lift f
    exact ⟨X, i, p, hi, hG.weak p hp, he⟩

end CategoryTheory.Waldhausen
