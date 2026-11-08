/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Product.Structure
public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory

/-! # Componentwise enlargement of product weak equivalences

Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductChangeWeak.lean:27–32` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, coordinates and path concatenations are retained. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory

universe u v

namespace CategoryTheory.Waldhausen.Product

open Fibration

variable {C : Type u} [Category.{v} C] (W : Structure C) (N : NestedWeakEquivalences W)

/-- The actual componentwise enlargement retains the original product cofibrations and zero. -/
def nestedWeakEquivalences : NestedWeakEquivalences (productStructure W W) where
  coarse := productStructure N.coarse N.coarse
  cof_eq := congrArg₂ MorphismProperty.prod N.cof_eq N.cof_eq
  zero_eq := congrArg₂ Prod.mk N.zero_eq N.zero_eq
  le_weq _ _ _ h := ⟨N.le_weq _ h.1, N.le_weq _ h.2⟩


end CategoryTheory.Waldhausen.Product
