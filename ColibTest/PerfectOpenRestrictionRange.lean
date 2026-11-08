/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectOpenRestrictionRange

/-! The actual degree-zero range equality has no qcqs assumption or open-surjectivity premise. -/

open CategoryTheory AlgebraicGeometry Scheme.Modules Waldhausen

noncomputable section

universe u

example {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (perfectOpenKRestrict j 0).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range :=
  range_perfectOpenKRestrict_zero j
