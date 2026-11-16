/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.LocalCoefficients.OpenExcision

/-! # Acyclicity of the actual relative complex detects the original inclusion -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u

namespace FundamentalGroupoid.LocalCoefficients
variable {X : Type u} [TopologicalSpace X]

/-- Vanishing of the actual relative complex gives quasi-isomorphism of the
original subspace inclusion in every degree, including degree zero. -/
theorem pushforwardChainMap_quasiIso_of_relative_acyclic (U : Set X)
    (A : System.{u, u} X) (ha : (relativeSingularChainComplex U A).Acyclic) :
    QuasiIso (pushforwardChainMap (subspaceInclusion U) A) := by
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion U) A)
      (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₁ (n + 1) n (by simp)).mono_g_iff.mpr
      ((ha (n + 1)).isZero_homology.eq_of_src _ _)
  have he : Epi (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₂ n).epi_f_iff.mpr ((ha n).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap S.f n)

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SubspaceAcyclicQuasiIso.lean:24-39"
  "adaptation" "The actual inclusion, including degree zero"]
  pushforwardChainMap_quasiIso_of_relative_acyclic

end FundamentalGroupoid.LocalCoefficients
