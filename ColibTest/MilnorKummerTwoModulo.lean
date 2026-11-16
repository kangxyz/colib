/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.EtaleCohomology.MilnorKummerTwoModulo

/-! # Regression checks for the original ordered degree-two Kummer symbol -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.EtaleCohomology.MilnorKummer
open scoped TensorProduct

noncomputable section
universe u

variable (k : Type u) [Field k] (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

example (a b : Additive kˣ) :
    milnorTwoModuloKummerSymbol k n
      (QuotientAddGroup.mk (milnorKTwoToKGroup k (a ⊗ₜ[ℤ] b))) =
        fieldUnitKummerCup k n a b :=
  milnorTwoModuloKummerSymbol_pair k n a b

example (x : MilnorKTheory k 2) : n • milnorTwoKummerSymbol k n x = 0 :=
  nsmul_milnorTwoKummerSymbol k n x
