/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Topology.LocalCoefficients.SphericalRelativeCycle
public import Colib.Topology.LocalCoefficients.RelativeFiniteBoundary

/-! # Actual point-relative cycles, quotients and finite boundaries -/
@[expose] public noncomputable section
open CategoryTheory Limits Topology
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X : Type u} [TopologicalSpace X] (z : X) (V : ModuleCat.{u} ℤ)

example (n : ℕ) : (pointRelativeHomologyIso z V n).hom =
    HomologicalComplex.homologyMap
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z}) (constant X V))) (n + 1) :=
  pointRelativeHomologyIso_hom z V n

-- Degree one really uses the split H₀ inclusion, not vanishing of H₀(point).
example : IsIso (HomologicalComplex.homologyMap (pointRelativeSequence z V).g 1) :=
  pointRelativeQuotient_homology_isIso z V 0

example {n : ℕ} (f : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).iCycles
      (n + 1) (sphericalRelativeCycle f) =
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficients.{u}))).f (n + 1)
        (chainInclusion (constant X integralCoefficients.{u}) f.val (ULift.up 1)) :=
  iCycles_sphericalRelativeCycle f

example {n : ℕ} (f : SphericalSimplex X z (n + 1))
    (h : (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).homologyπ
      (n + 1) (sphericalRelativeCycle f) = 0) :
    ∃ (s : Finset (SingularSimplex X ⦋n + 2⦌)) (a : ∀ σ,
      simplexFiber (constant X integralCoefficients.{u}) σ),
      (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).d
        (n + 2) (n + 1)
        ((cokernel.π (pushforwardChainMap (subspaceInclusion {z})
          (constant X integralCoefficients.{u}))).f (n + 2)
            (∑ σ ∈ s, chainInclusion (constant X integralCoefficients.{u}) σ (a σ))) =
      sphericalRelativeChain f := by
  obtain ⟨s, a, ha⟩ := relativeCycle_exists_finite_boundary {z}
    (constant X integralCoefficients.{u}) (n + 1) (sphericalRelativeCycle f) h
  exact ⟨s, a, ha.trans (iCycles_sphericalRelativeCycle f)⟩

example (W : Set X) (A : System.{u, u} X) (n : ℕ)
    (c : (relativeSingularChainComplex W A).cycles n)
    (hc : (relativeSingularChainComplex W A).homologyπ n c = 0) :
    ∃ b, (relativeSingularChainComplex W A).d (n + 1) n b =
      (relativeSingularChainComplex W A).iCycles n c :=
  chainCycle_boundary_of_homology_eq_zero _ n c hc

example {G : Type u} [AddCommGroup G] (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (hv : v (ContinuousMap.const _ z) = 0)
    (a b : chainModule (constant X integralCoefficients.{u}) ⦋n⦌)
    (hab : (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
      (constant X integralCoefficients.{u}))).f n a =
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficients.{u}))).f n b) :
    integralChainEvaluation n v a = integralChainEvaluation n v b :=
  integralChainEvaluation_eq_of_pointRelative_eq z n v hv a b hab

end FundamentalGroupoid.LocalCoefficients
