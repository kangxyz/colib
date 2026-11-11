/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak
public import Colib.CategoryTheory.Waldhausen.Fibration.ExactChangeWeak

/-!
# Original inverse equivalences for inverse-image weak structures

A genuine fine exact equivalence remains exact in both directions after enlarging the target
weak class and pulling that class back along its original forward functor. The original
counit proves inverse preservation of the coarse weak maps; no coarse exactness is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {V : Structure C} {W : Structure D} (e : C ≌ D)
  (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)
  (N : Fibration.NestedWeakEquivalences W)

include hG in
/-- The original inverse is exact for the actual pulled-back enlarged weak class. -/
@[colib_ref "quillen" "Quillen/Waldhausen/Fibration/InverseImageWeakEquivalence.lean:30-48"
  "adaptation" "Exactness of the original inverse for the enlarged target weak class"]
theorem Structure.withInverseImageWeak_inverse_exact :
    IsExact N.coarse.cof N.coarse.weq
      (Structure.withInverseImageWeak (hF.changeWeakTarget N)).cof
      (Structure.withInverseImageWeak (hF.changeWeakTarget N)).weq e.inverse where
  zero := hG.zero
  cofibration f hf := hG.cofibration f (by rwa [N.cof_eq] at hf)
  weak f hf := by
    change N.coarse.weq (e.functor.map (e.inverse.map f))
    have hm : e.functor.map (e.inverse.map f) =
        e.counitIso.hom.app _ ≫ f ≫ e.counitIso.inv.app _ := by
      simpa only [Functor.comp_map, Functor.id_map, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id] using
        congrArg (fun k => k ≫ e.counitIso.inv.app _)
          (e.counitIso.hom.naturality f)
    rw [hm]
    exact N.coarse.weq.comp_mem _ _ (N.coarse.weq_iso _ inferInstance)
      (N.coarse.weq.comp_mem _ _ hf (N.coarse.weq_iso _ inferInstance))
  pushout hi hp := hG.pushout (by rwa [N.cof_eq] at hi) hp

end CategoryTheory.Waldhausen
