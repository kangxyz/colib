/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Approximation.DualInverseImageLift

/-! Regression checks for the original K-map, including K-zero and fine lifts without reflection. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen Topology

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  {U : Structure E} {Ud : Structure Eᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd)
  (hU : IsCompatibleDual U Ud) {F : C ⥤ D} {G : D ⥤ E}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (hG : IsExact V.cof V.weq U.cof U.weq G)
  (hGd : IsExact Vd.cof Vd.weq Ud.cof Ud.weq G.op)
  (Jd : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))

section DualApproximation

variable [V.weq.HasTwoOutOfThreeProperty]
  (h : HasDualApproximationProperty W V Wd.cof.unop F)

example : IsWeakHomotopyEquivalence (deloopingMap hF).hom :=
  deloopingMap_isWeakHomotopyEquivalence_of_dualApproximation hW hV hF hFd h Jd

example (n : ℕ) : Function.Bijective (KMap hF n) :=
  KMap_bijective_of_dualApproximation hW hV hF hFd h Jd n

example : W.K 0 ≃* V.K 0 := KEquivOfDualApproximation hW hV hF hFd h Jd 0

example (n : ℕ) :
    (↑(KEquivOfDualApproximation hW hV hF hFd h Jd n) : W.K n →* V.K n) =
      KMap hF n := rfl

end DualApproximation

section FineLiftOnly

variable [U.weq.HasTwoOutOfThreeProperty]
  (hlift : ∀ {X : C} {Y : D} (f : Y ⟶ F.obj X),
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      Wd.cof.unop i ∧ V.weq p ∧ p ≫ F.map i = f)

-- There is deliberately no fine reflection or saturation assumption on V here.
example : HasDualApproximationProperty (Structure.withInverseImageWeak (hF.comp hG))
    (Structure.withInverseImageWeak hG) Wd.cof.unop F :=
  dualApproximation_of_inverseImageLift hF hG hlift

example : Function.Bijective (KMap (inverseImageComposite_exact hF hG) 0) :=
  KMap_bijective_of_dualLift_inverseImage hW hV hU hF hFd hG hGd hlift Jd 0

example (n : ℕ) : Function.Bijective (KMap (inverseImageComposite_exact hF hG) n) :=
  KMap_bijective_of_dualLift_inverseImage hW hV hU hF hFd hG hGd hlift Jd n

example {A B : C} (f : A ⟶ B) :
    (Structure.withInverseImageWeak (hF.comp hG)).weq f ↔
      U.weq (G.map (F.map f)) := Iff.rfl

end FineLiftOnly

section LiteralJointMaps

variable {N : Fibration.NestedWeakEquivalences Wd}
  [N.coarse.weq.HasTwoOutOfThreeProperty] (f : Arrow Cᵒᵖ)

example : (Jd.toCoarse N).projection.app f = Jd.projection.app f := rfl
example : (Jd.toCoarse N).inl.app f = Jd.inl.app f := rfl
example : (Jd.toCoarse N).inr.app f = Jd.inr.app f := rfl
example : ((Jd.toCoarse N).joint.obj f).obj.hom = (Jd.joint.obj f).obj.hom := rfl

end LiteralJointMaps
