/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy

/-! Whole-level transport along equality of the actual exact functor isomorphism. -/
@[expose] public noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.IteratedS

/-- An equality of the actual isomorphisms retains the entire realized level track. -/
theorem exactOriginalPrespectrumIsoHomotopy_congr_level
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) {F G : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact W.cof W.weq V.cof V.weq G)
    (i j : F ≅ G) (h : i = j) (n : ℕ) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hG i).level n =
      (exactOriginalPrespectrumIsoHomotopy W V hF hG j).level n := by
  cases h
  rfl

end CategoryTheory.Waldhausen.IteratedS
