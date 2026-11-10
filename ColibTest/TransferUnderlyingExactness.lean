/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.UnderlyingExactness

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

example : PreservesFiniteColimits (SheafWithTransfers.toSheaf.{u + 1} k) := inferInstance

example (S : ShortComplex (SheafWithTransfers.{u + 1} k)) :
    (S.map (SheafWithTransfers.toSheaf k)).Exact ↔ S.Exact :=
  SheafWithTransfers.exact_toSheaf_iff k S

example {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) :
    (SheafWithTransfers.toSheaf k).obj (cokernel f) ≅
      cokernel ((SheafWithTransfers.toSheaf k).map f) :=
  SheafWithTransfers.underlyingCokernelIso k f
