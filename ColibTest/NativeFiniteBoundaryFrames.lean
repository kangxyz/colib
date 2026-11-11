/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteBoundaryFrames
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
variable {B Z : Scheme.{u}} (b : Z ⟶ B) [IsFinite b]
example (x : B) (U : B.Opens) (hx : x ∈ U) :
    b ⁻¹' {x} ⊆ (b ⁻¹ᵁ U : Set Z) := wholeFiniteBoundary_fiber_retained b x U hx
example {K : Type u} [Field K] (z : Spec (.of K) ⟶ B)
    (a : Spec (.of K)) (U : B.Opens) (h : z a ∈ U) : Set.range z ⊆ U :=
  fieldMark_range_subset z a U h
#check exists_wholeFiniteBoundary_pair_frames
#check exists_wholeFiniteBoundary_power_frames
#check exists_wholeFiniteBoundary_power_frames_at_fieldMark
