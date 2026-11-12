/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Cube.SimplexPair
public import Colib.Topology.HELP.RealizedSimplexBoundary
public import Colib.CategoryTheory.TheoremA.EnrichedBoundaryHEP
public import Colib.Topology.Realization.MonomorphismLifting

/-!
# Cube-boundary lifting implies lifting over realized simplicial inclusions

The actual cube/simplex boundary-pair homeomorphism transports literal finite
cube-boundary lifts to the realized standard-simplex inclusions. The relative
skeletal construction then supplies lifts over every realized simplicial
monomorphism, without a compact HELP or CW-type hypothesis.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/CubicalLifting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The existing realized-boundary lifting theorem is reused; the simplex-pair and
realized-monomorphism arguments are retained. -/

@[expose] public section
noncomputable section

open CategoryTheory Convexity
open scoped Topology Simplicial unitInterval

universe u v
namespace Topology.CubicalSubdivision

/-- Strict cube-boundary lifting transports across the genuine simplex pair
homeomorphism, retaining the entire prescribed boundary map. -/
theorem BoundaryLifting.simplex
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : BoundaryLifting p) (n : ℕ)
    (a : C(Convexity.StdSimplex.boundary n, E)) (b : C(StdSimplex ℝ (Fin (n + 1)), B))
    (hab : ∀ x : Convexity.StdSimplex.boundary n, p (a x) = b x.val) :
    ∃ c : C(StdSimplex ℝ (Fin (n + 1)), E),
      (∀ x : Convexity.StdSimplex.boundary n, c x.val = a x) ∧ p.comp c = b := by
  let e := Topology.Cube.simplexHomeomorph n
  let d := Topology.Cube.simplexBoundaryHomeomorph n
  let a' := a.comp d.toHomotopyEquiv.toFun
  let b' := b.comp e.toHomotopyEquiv.toFun
  obtain ⟨c, hc, he⟩ := hp n a' b' (fun x ↦ hab (d x))
  refine ⟨c.comp e.symm.toHomotopyEquiv.toFun, ?_, ?_⟩
  · intro x
    have h := hc (d.symm x)
    change c (e.symm x.val) = a (d (d.symm x)) at h
    change c (e.symm x.val) = a x
    simpa only [Homeomorph.apply_symm_apply] using h
  · apply ContinuousMap.ext
    intro x
    have h := ContinuousMap.congr_fun he (e.symm x)
    change p (c (e.symm x)) = b (e (e.symm x)) at h
    change p (c (e.symm x)) = b x
    simpa only [Homeomorph.apply_symm_apply] using h

/-- A map with literal finite cube-boundary lifting lifts over every original
realized simplicial monomorphism. -/
theorem BoundaryLifting.hasLiftingProperty_realization_mono
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : BoundaryLifting p)
    {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) (TopCat.ofHom p) :=
  SSet.hasLiftingProperty_realization_mono (TopCat.ofHom p)
    hp.hasLiftingProperty_realizationBoundary i

end Topology.CubicalSubdivision
