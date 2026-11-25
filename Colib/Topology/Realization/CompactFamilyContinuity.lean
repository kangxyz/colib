/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Realization.FiniteHausdorff
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Compact parameter families from joint characteristic-simplex continuity

A proper finite characteristic-simplex cover proves the finite realization
case. Exact finite support then gives the compact parameter statement. The
evaluator remains a supplied well-defined function, and joint continuity on
each characteristic simplex times the entire input space is an explicit
hypothesis. No hypothesis is imposed on the input beyond its topology.

Adapted from `Quillen/Topology/Realization/CompactFamilyContinuity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the finite characteristic cover
and the actual finite subcomplex factorization.
-/
@[expose] public section

noncomputable section
open CategoryTheory Topology
open scoped Simplicial Topology
universe u v w z
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet

/-- A finite realization admits quotient descent after product with any
topological input, using its proper finite characteristic-simplex cover. -/
private theorem realization_finiteFamily_continuous
    (S : SSet.{u}) [S.Finite]
    {E : Type w} {Z : Type z}
    [TopologicalSpace E] [TopologicalSpace Z]
    (ev : |S| × E → Z)
    (hsimplex : ∀ (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ S),
      Continuous (fun y : |(Δ[n] : SSet.{u})| × E ↦
        ev (SSet.toTop.map σ y.1, y.2))) :
    Continuous ev := by
  let Q := Σ s : S.N, |(Δ[s.dim] : SSet.{u})|
  let q : Q → |S| :=
    fun y ↦ SSet.toTop.map (SSet.yonedaEquiv.symm y.1.simplex) y.2
  have hq : Continuous q := by
    apply continuous_sigma
    intro s
    exact (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous
  have hqs : Function.Surjective q := by
    intro a
    obtain ⟨s, t, ht⟩ := realization_nonDegenerate_jointly_surjective S a
    exact ⟨⟨s, t⟩, ht⟩
  have hquot : IsQuotientMap (Prod.map q (id : E → E)) :=
    (hq.isProperMap.prodMap isProperMap_id).isClosedMap.isQuotientMap
      (hq.prodMap continuous_id) (hqs.prodMap Function.surjective_id)
  let F : (Σ s : S.N, |(Δ[s.dim] : SSet.{u})| × E) → Z :=
    fun y ↦ ev (SSet.toTop.map (SSet.yonedaEquiv.symm y.1.simplex) y.2.1, y.2.2)
  have hF : Continuous F := by
    apply continuous_sigma
    intro s
    exact hsimplex s.dim (SSet.yonedaEquiv.symm s.simplex)
  have hcover : Continuous (ev ∘ Prod.map q (id : E → E)) :=
    hF.comp Homeomorph.sigmaProdDistrib.continuous
  exact hquot.continuous_iff.mpr hcover

/-- Joint continuity on each original characteristic simplex gives joint
continuity after any compact parameter map. No separation, compactness, or
local compactness hypothesis is imposed on the input space `E`. -/
theorem realization_compactFamily_continuous
    (S : SSet.{u})
    {E : Type w} {Z : Type z}
    [TopologicalSpace E] [TopologicalSpace Z]
    (ev : |S| × E → Z)
    (hsimplex : ∀ (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ S),
      Continuous (fun y : |(Δ[n] : SSet.{u})| × E ↦
        ev (SSet.toTop.map σ y.1, y.2)))
    {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (p : C(T, |S|)) :
    Continuous (fun y : T × E ↦ ev (p y.1, y.2)) := by
  obtain ⟨A, hA, g, hg⟩ := realization_continuousMap_factors_finiteSubcomplex p
  let : SSet.Finite (A : SSet.{u}) := hA
  let evA : |(A : SSet.{u})| × E → Z :=
    fun y ↦ ev (SSet.toTop.map A.ι y.1, y.2)
  have hevA : Continuous evA := by
    apply realization_finiteFamily_continuous (A : SSet.{u}) evA
    intro n σ
    change Continuous (fun y : |(Δ[n] : SSet.{u})| × E ↦
      ev (SSet.toTop.map A.ι (SSet.toTop.map σ y.1), y.2))
    simpa only [Functor.map_comp, TopCat.comp_app] using hsimplex n (σ ≫ A.ι)
  have h : Continuous (fun y : T × E ↦
      ev (SSet.toTop.map A.ι (g y.1), y.2)) :=
    hevA.comp (g.continuous.prodMap (continuous_id : Continuous (id : E → E)))
  have he : (fun y : T × E ↦ ev (p y.1, y.2)) =
      (fun y : T × E ↦ ev (SSet.toTop.map A.ι (g y.1), y.2)) := by
    funext y
    exact congrArg (fun a ↦ ev (a, y.2)) (ContinuousMap.congr_fun hg y.1).symm
  rw [he]
  exact h

end SSet
