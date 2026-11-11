/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeGraphDivisor

/-! Relative graph scope checks without an absolute field-curve assumption. UNCOMPILED. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

universe u

variable {S X V : Scheme.{u}} (q : X ⟶ S) (r : V ⟶ S)
  [IsSeparated r] [SmoothOfRelativeDimension 1 r] (φ : X ⟶ V) (hφ : φ ≫ r = q)

example : IsEffectiveCartierDivisor (relativeGraphIdeal q r φ hφ) := inferInstance

example : Flat ((relativeGraphIdeal q r φ hφ).subschemeι ≫ pullback.fst q r) :=
  (relativeCartier_relativeGraphIdeal q r φ hφ).2

example : Stacks.Divisors.zeroScheme (pullback q r) (divisorSheaf (relativeGraphIdeal q r φ hφ))
    (divisorSheafGlobalSection (relativeGraphIdeal q r φ hφ)) = relativeGraphIdeal q r φ hφ :=
  zeroScheme_relativeGraphCanonicalSection q r φ hφ

#check relativeGraphSupportIso
#check relativeGraphSupportIso_hom_base
#check relativeGraphSupportIso_hom_target
#check relativeGraphSupportIso_hom_graph
