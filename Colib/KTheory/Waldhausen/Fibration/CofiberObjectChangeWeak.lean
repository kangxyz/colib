/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberObjectTrack
public import Colib.CategoryTheory.Waldhausen.Fibration.CofiberObjectChangeWeak

/-! # The original fine cofiber track through the localization map -/
/-! Implementation provenance: `Quillen/Waldhausen/Fibration/CofiberObjectChangeWeak.lean`
lines 46–56 at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Both original cofibration and pushout certificates and both times are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite SSet
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {V : Structure C} (N : NestedWeakEquivalences V)
  {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : V.cof i) (hi' : N.coarse.cof i)
  (hQ : IsPushout i (0 : A ⟶ V.zero) q (0 : V.zero ⟶ Q))
  (hQ' : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- The entire original triangle homotopy retains both comparison and object-loop time. -/
theorem cofiberObjectLoopTrack_changeWeak (r t : unitInterval) :
    changeWeakMap N (V.cofiberObjectLoopTrack i q hi hQ (r, t)) =
      N.coarse.cofiberObjectLoopTrack i q hi' hQ' (r, t) := by
  rw [Structure.cofiberObjectLoopTrack_apply, Structure.cofiberObjectLoopTrack_apply,
    realizationEdgeCompositionHomotopy_apply, realizationEdgeCompositionHomotopy_apply]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (V.cofiberObjectSimplex i q hi hQ)) ≫
    SSet.toTop.map (sSetMap (changeWeak_exact N))) _ = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp,
    cofiberObjectSimplex_changeWeak N i q hi hi' hQ hQ']
  rfl

attribute [colib_tag "COL-0299"] cofiberObjectLoopTrack_changeWeak

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/CofiberObjectChangeWeak.lean:47-56" "adaptation"
  "The whole fine cofiber triangle maps to its literal coarse triangle at both independent
    times, retaining both cofibration and both displayed pushout certificates"]
  cofiberObjectLoopTrack_changeWeak

end CategoryTheory.Waldhausen.Fibration
