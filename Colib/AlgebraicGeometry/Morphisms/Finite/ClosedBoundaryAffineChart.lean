/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
/-! # Whole finite boundaries contained in an affine projective chart

A closed boundary in a proper scheme which misses the complementary hyperplane
is finite over an affine base. The original closed scheme is retained, with
no reducedness or flatness assumption.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Properness plus an actual affine-chart factorization proves finiteness. -/
theorem isFinite_closed_boundary_in_affine_chart {C S B : Scheme.{u}}
    (p : C ⟶ S) [IsProper p] [IsAffine S]
    (i : B ⟶ C) [IsClosedImmersion i]
    (U : C.Opens) (hU : IsAffineOpen U) (h : Set.range i ⊆ U) :
    IsFinite (i ≫ p) := by
  let g := IsOpenImmersion.lift U.ι i (by simpa using h)
  have hp := IsOpenImmersion.isPullback_lift_id i U.ι (by simpa using h)
  have : IsClosedImmersion g := by
    change IsClosedImmersion (IsOpenImmersion.lift U.ι i _)
    rw [← hp.isoPullback_hom_fst]
    infer_instance
  have : IsAffine U := hU
  have : IsAffine B := isAffine_of_isAffineHom g
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
