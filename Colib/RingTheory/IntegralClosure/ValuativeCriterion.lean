/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # An elementwise valuative criterion for the original ring map

The source need not inject into the field. Its actual image is used internally,
and integrality is descended along the surjection onto that image.
-/
@[expose] public noncomputable section

namespace RingHom

/-- An element lying in every valuation ring containing the actual source image
is integral for the original ring map, with no injectivity hypothesis. -/
theorem isIntegralElem_of_mem_valuationSubrings
    {A F : Type*} [CommRing A] [Field F] (f : A →+* F) (x : F)
    (h : ∀ V : ValuationSubring F, f.range ≤ V.toSubring → x ∈ V) :
    f.IsIntegralElem x := by
  let : Algebra A F := f.toAlgebra
  let : Algebra A f.range := f.rangeRestrict.toAlgebra
  let : IsScalarTower A f.range F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsIntegral A f.range :=
    ⟨f.rangeRestrict.isIntegral_of_surjective f.rangeRestrict_surjective⟩
  have hx : x ∈ (⨅ V : {V : ValuationSubring F //
      (f.range : Set F) ⊆ V.toSubring}, V.1.toSubring) := by
    exact Subring.mem_iInf.mpr fun V => h V.1 V.2
  rw [iInf_valuationSubring_superset] at hx
  have hclosure := congrArg (fun S : Subring F => (_root_.integralClosure S F).toSubring)
    (Subring.closure_eq f.range)
  rw [hclosure] at hx
  have hx' : _root_.IsIntegral f.range x := hx
  exact isIntegral_trans x hx'

end RingHom
