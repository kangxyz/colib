/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.LocalCoefficients.ChainSupport
public import Colib.Topology.LocalCoefficients.SmallChainExcision
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Actual finite singular-chain witnesses for zero relative cycle classes -/
@[expose] public section
noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients

/-- Vanishing in the genuine categorical homology quotient gives an actual chain boundary. -/
theorem chainCycle_boundary_of_homology_eq_zero
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (z : K.cycles n)
    (hz : K.homologyπ n z = 0) :
    ∃ b : K.X (n + 1), K.d (n + 1) n b = K.iCycles n z := by
  have hp : K.pOpcycles n (K.iCycles n z) = 0 := by
    have h := ConcreteCategory.congr_hom (K.homology_π_ι n) z
    simpa only [ModuleCat.comp_apply, hz, map_zero] using h.symm
  have hb := (K.sc n).moduleCat_pOpcycles_eq_zero_iff _ |>.mp hp
  change ∃ b : K.X ((ComplexShape.down ℕ).prev n),
    K.d ((ComplexShape.down ℕ).prev n) n b = K.iCycles n z at hb
  rw [ChainComplex.prev ℕ n] at hb
  exact hb

variable {X : Type u} [TopologicalSpace X] (W : Set X) (A : System.{u, u} X)

/-- A zero relative cycle class is the boundary of the quotient of a finite sum
of actual ambient singular simplices, with their original coefficient fibers. -/
theorem relativeCycle_exists_finite_boundary (n : ℕ)
    (z : (relativeSingularChainComplex W A).cycles n)
    (hz : (relativeSingularChainComplex W A).homologyπ n z = 0) :
    ∃ (s : Finset (SingularSimplex X ⦋n + 1⦌)) (a : ∀ simplex, simplexFiber A simplex),
      (relativeSingularChainComplex W A).d (n + 1) n
        ((cokernel.π (pushforwardChainMap (subspaceInclusion W) A)).f (n + 1)
          (∑ simplex ∈ s, chainInclusion A simplex (a simplex))) =
        (relativeSingularChainComplex W A).iCycles n z := by
  obtain ⟨b, hb⟩ := chainCycle_boundary_of_homology_eq_zero _ n z hz
  let q := cokernel.π (pushforwardChainMap (subspaceInclusion W) A)
  have : Epi (q.f (n + 1)) := by
    change Epi ((HomologicalComplex.eval _ _ (n + 1)).map q)
    infer_instance
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (q.f (n + 1))).mp inferInstance b
  obtain ⟨s, a, ha⟩ := chain_exists_finite_sum A ⦋n + 1⦌ c
  refine ⟨s, a, ?_⟩
  exact (congrArg (fun c : chainModule A ⦋n + 1⦌ ↦
    (relativeSingularChainComplex W A).d (n + 1) n (q.f (n + 1) c)) ha.symm).trans
      ((congrArg ((relativeSingularChainComplex W A).d (n + 1) n) hc).trans hb)

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RelativeFiniteBoundary.lean:24-40"
  "adaptation" "Actual point quotient and original finite singular chains"]
  chainCycle_boundary_of_homology_eq_zero

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/RelativeFiniteBoundary.lean:41-59"
  "adaptation" "Actual point quotient and original finite singular chains"]
  relativeCycle_exists_finite_boundary

attribute [colib_tag "COL-0526"]
  relativeCycle_exists_finite_boundary

end FundamentalGroupoid.LocalCoefficients
