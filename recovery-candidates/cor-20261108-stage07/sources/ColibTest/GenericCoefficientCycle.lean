/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Chow.GenericCoefficientCycle

/-! Source-only semantic tests. These require the parent's serialized Lean guard. -/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicCycle TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u v

variable {X : Scheme.{u}} {R : Type v} [AddCommGroup R]
variable (hfin : (genericPoints X).Finite)

-- The value really is a native algebraic cycle, with no intermediate cycle model.
example (c : genericPoints X → R) : AlgebraicCycle X R :=
  ofGenericCoefficients hfin c

-- Every actual generic point, including those of disconnected schemes, is retained.
example (c : genericPoints X → R) (x : genericPoints X) :
    ofGenericCoefficients hfin c x.val = c x :=
  ofGenericCoefficients_apply_generic hfin c x

example (c : genericPoints X → R) (x : X) (hx : x ∉ genericPoints X) :
    ofGenericCoefficients hfin c x = 0 :=
  ofGenericCoefficients_apply_of_notMem hfin c x hx

example (x : genericPoints X) (r : R) :
    ofGenericCoefficients hfin (Pi.single x r) = single x.val r :=
  ofGenericCoefficients_single hfin x r

-- No compactness or Noetherian hypothesis is smuggled into finite support.
example (c : genericPoints X → R) : (ofGenericCoefficients hfin c).support.Finite :=
  finite_support_ofGenericCoefficients hfin c

example (c : genericPoints X → R) :
    (ofGenericCoefficients hfin c).support = Subtype.val '' Function.support c :=
  support_ofGenericCoefficients hfin c

-- This is an actual reconstruction equality, not an assumed comparison field.
example (D : AlgebraicCycle X R) (hD : D.support ⊆ genericPoints X) :
    ofGenericCoefficients hfin (fun x => D x.val) = D :=
  ofGenericCoefficients_eq_self hfin D hD

example (c d : genericPoints X → R) :
    ofGenericCoefficients hfin c = ofGenericCoefficients hfin d ↔ c = d :=
  ofGenericCoefficients_eq_iff hfin c d

-- Negative coefficients and integer multiplicities survive unchanged.
example (c : genericPoints X → ℤ) (x : genericPoints X) :
    ofGenericCoefficients hfin (-c) x.val = -c x := by
  simp

example (c d : genericPoints X → ℤ) :
    ofGenericCoefficients hfin (c - d) =
      ofGenericCoefficients hfin c - ofGenericCoefficients hfin d :=
  ofGenericCoefficients_sub hfin c d

example (n : ℤ) (c : genericPoints X → R) :
    ofGenericCoefficients hfin (n • c) = n • ofGenericCoefficients hfin c :=
  ofGenericCoefficients_zsmul hfin n c

-- Finite alternating-sum assembly follows from the genuine additive map.
example (s : Finset ℕ) (c : ℕ → genericPoints X → ℤ) :
    ofGenericCoefficients hfin (∑ n ∈ s, (-1 : ℤ) ^ n • c n) =
      ∑ n ∈ s, (-1 : ℤ) ^ n • ofGenericCoefficients hfin (c n) := by
  simp only [map_sum, ofGenericCoefficients_zsmul]

-- The empty scheme contributes the zero cycle.
example [IsEmpty X] (c : genericPoints X → R) : ofGenericCoefficients hfin c = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact isEmptyElim x
