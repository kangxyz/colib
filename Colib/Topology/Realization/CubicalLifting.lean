/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Cube.SimplexPair
public import Colib.Topology.CubicalSubdivision.BoundaryLifting
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
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

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

/-- Literal cube-boundary lifting gives strict lifting against the original
realization of every standard-simplex boundary inclusion. -/
theorem BoundaryLifting.hasLiftingProperty_realizationBoundary
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : BoundaryLifting p) (n : ℕ) :
    HasLiftingProperty (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})))
      (TopCat.ofHom p) where
  sq_hasLift {a b} sq := by
    let d := realizationBoundaryHomeomorph.{u} n
    let e := SimplexCategory.toTopHomeo.{u} ⦋n⦌
    let a' : C(Convexity.StdSimplex.boundary n, E) := a.hom.comp d.symm.toHomotopyEquiv.toFun
    let b' : C(StdSimplex ℝ (Fin (n + 1)), B) :=
      b.hom.comp e.symm.toHomotopyEquiv.toFun
    have hinc (x : |(∂Δ[n] : SSet.{u})|) :
        (d x).val = e (SSet.toTop.map ∂Δ[n].ι x) := rfl
    have hab (x : Convexity.StdSimplex.boundary n) : p (a' x) = b' x.val := by
      have h := ConcreteCategory.congr_hom sq.w (d.symm x)
      change p (a (d.symm x)) = b (SSet.toTop.map ∂Δ[n].ι (d.symm x)) at h
      have hx : SSet.toTop.map ∂Δ[n].ι (d.symm x) = e.symm x.val := by
        apply e.injective
        rw [← hinc, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
      change p (a (d.symm x)) = b (e.symm x.val)
      simpa only [hx] using h
    obtain ⟨c, hc, he⟩ := hp.simplex n a' b' hab
    refine ⟨TopCat.ofHom (c.comp e.toHomotopyEquiv.toFun), ?_, ?_⟩
    · apply ConcreteCategory.hom_ext
      intro x
      change c (e (SSet.toTop.map ∂Δ[n].ι x)) = a x
      rw [← hinc, hc]
      change a (d.symm (d x)) = a x
      rw [Homeomorph.symm_apply_apply]
    · apply ConcreteCategory.hom_ext
      intro x
      have h := ContinuousMap.congr_fun he (e x)
      change p (c (e x)) = b (e.symm (e x)) at h
      change p (c (e x)) = b x
      simpa only [Homeomorph.symm_apply_apply] using h

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
