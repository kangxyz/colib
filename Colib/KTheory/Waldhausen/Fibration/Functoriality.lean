/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.Functoriality
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap

/-!
# Naturality of the original inclusion and change-of-weak maps

The actual functor on coarse-acyclic categories gives strict realization
squares and canonical K-map squares. No comparison square is an assumption.

Implementation provenance: adapted from
`Quillen/Waldhausen/Fibration/Functoriality.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual objects, functors,
chosen zero data, exactness witnesses and shared universe pair are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

/-- The original change-of-weak realization maps form a strict square. -/
lemma changeWeakMap_natural :
    (deloopingMap hFc).hom.comp (changeWeakMap N) =
      (changeWeakMap M).comp (deloopingMap hF).hom := by
  rw [changeWeakMap, changeWeakMap]
  rw [← TopCat.hom_comp, ← TopCat.hom_comp,
    deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]

/-- The original acyclic-inclusion realization maps form a strict square. -/
lemma acyclicInclusionMap_natural :
    (deloopingMap hF).hom.comp (acyclicInclusionMap N) =
      (acyclicInclusionMap M).comp (deloopingMap (acyclicFunctor_exact N M hF hFc)).hom := by
  rw [acyclicInclusionMap, acyclicInclusionMap]
  rw [← TopCat.hom_comp, ← TopCat.hom_comp,
    deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]

/-- Changing weak equivalences commutes with the actual canonical K-maps. -/
lemma changeWeakKMap_natural (n : ℕ) :
    (KMap hFc n).comp (KMap (changeWeak_exact N) n) =
      (KMap (changeWeak_exact M) n).comp (KMap hF n) := by
  rw [KMap_comp_KMap, KMap_comp_KMap]

/-- The original acyclic-inclusion K-maps commute in every degree. -/
lemma acyclicInclusionKMap_natural (n : ℕ) :
    (KMap hF n).comp (KMap (acyclicInclusion_exact N) n) =
      (KMap (acyclicInclusion_exact M) n).comp (KMap (acyclicFunctor_exact N M hF hFc) n) := by
  rw [KMap_comp_KMap, KMap_comp_KMap]


end CategoryTheory.Waldhausen.Fibration
