/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.Algebra.Homology.ArrowPostcompose
/-! # Complete original composition data before interpreting the composite Arrow -/
@[expose] public noncomputable section
open CategoryTheory
/-- Retain both arrows and their original matching endpoint. -/
structure ArrowCompositionData (C : Type*) [Category C] where
  /-- The first arrow, retained before composition. -/
  first : Arrow C
  /-- The second arrow, retained before composition. -/
  second : Arrow C
  target_eq : first.right = second.left
variable {C : Type*} [Category C]
/-- Interpret only the stored composition data. -/
def ArrowCompositionData.toArrow (d : ArrowCompositionData C) : Arrow C :=
  arrowPostcompose d.first d.second d.target_eq
/-- Change an independently certified first arrow, keeping the complete second arrow. -/
def ArrowCompositionData.replaceFirst (d : ArrowCompositionData C)
    (a : Arrow C) (h : d.first = a) : ArrowCompositionData C :=
  ⟨a, d.second, (congrArg Arrow.right h).symm.trans d.target_eq⟩
/-- Replacement of equal input data preserves the interpreted composite. -/
theorem ArrowCompositionData.toArrow_replaceFirst (d : ArrowCompositionData C)
    (a : Arrow C) (h : d.first = a) :
    d.toArrow = (d.replaceFirst a h).toArrow :=
  arrowPostcompose_congr_left h _ _ _
