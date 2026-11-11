/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.ScalarTrace
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Basic

/-!
# Finite scalar trace on the original presheaf with transfers

This leaf proves the degree action and sectionwise annihilation. It does not
assert Cartesian trace naturality. All maps are the original signed
correspondence action. Neither homotopy
invariance nor a supplied trace or cohomological comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- The original scalar restriction followed by the actual trace multiplies
sections by the entire extension degree. -/
theorem finiteScalar_restriction_trace (X : SmoothSite (Spec (.of k))) :
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X)) ≫
        transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X)) =
      (Module.finrank k E : ℤ) • 𝟙 (sections P (Cor.mk X)) := by
  simpa only [transfer_comp, transfer_zsmul, transfer_id] using
    congrArg (transfer P) (Cor.finiteScalarTrace_comp_graph (E := E) X)

/-- A section killed by its actual scalar restriction is killed by the full
extension degree in its unchanged original section group. -/
theorem finrank_smul_eq_zero_of_scalar_restriction_eq_zero
    (X : SmoothSite (Spec (.of k))) (s : sections P (Cor.mk X))
    (hs : transfer P ((Cor.graphFunctor k).map
      (SmoothSite.finiteScalarProjection (E := E) X)) s = 0) :
    (Module.finrank k E : ℤ) • s = 0 := by
  have h := congrArg (fun f => f s) (finiteScalar_restriction_trace (E := E) P X)
  change transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X))
    (transfer P ((Cor.graphFunctor k).map
      (SmoothSite.finiteScalarProjection (E := E) X)) s) =
      (Module.finrank k E : ℤ) • s at h
  simpa only [hs, map_zero] using h.symm

end AlgebraicGeometry.PresheafWithTransfers
