/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageApproximation

/-! The exact geometric roof proposition is the only nonstructural input.
No joint-data, outgoing approximation, density or K-equivalence hypothesis occurs. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

example (hroof : HasDerivedRoofs j) (n : ℕ) :
    letI : Fact (HasDerivedRoofs j) := ⟨hroof⟩
    Function.Bijective (KMap (relativeCorestrict_isExact j) n) := by
  let : Fact (HasDerivedRoofs j) := ⟨hroof⟩
  exact relativeCorestrict_KMap_bijective j n

example (hroof : HasDerivedRoofs j) :
    letI : Fact (HasDerivedRoofs j) := ⟨hroof⟩
    PerfectOpenK j 0 ≃* (waldhausen j hroof).K 0 := by
  letI : Fact (HasDerivedRoofs j) := ⟨hroof⟩
  exact relativeCorestrictKEquiv j 0

example [Fact (HasDerivedRoofs j)] (n : ℕ) (x : PerfectOpenK j n) :
    KMap (inclusion_isExact j Fact.out) n (relativeCorestrictKEquiv j n x) =
      perfectOpenKRestrict j n x :=
  DFunLike.congr_fun (relativeKMap_factor j n) x
