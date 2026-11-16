/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.PullbackSimplyConnected
public import Colib.Topology.Covering.PullbackWeakEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceConnected
public import Colib.Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected
public import Colib.Topology.LocalCoefficients.PullbackCoveringHomology

/-!
# Homological Whitehead using a supplied simply connected target cover

The literal pullback of that cover is simply connected when the original map
is bijective on the fundamental group at the chosen matching pair. Its second
projection preserves integral singular chains, by the actual covering-fiber
coefficient system. Homological Whitehead and the projection square then
detect the original map. No independently supplied source cover or lift is
needed.

The supplied-cover descent argument adapts
`Quillen/Topology/LocalCoefficients/TwistedWhiteheadSuppliedCovers.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open CategoryTheory FundamentalGroupoid
open FundamentalGroupoid.LocalCoefficients.PullbackCovering
open scoped Topology
universe u

namespace Topology.LocalCoefficients

/-- Relate the based map to the same original map at its literal image point. -/
private theorem piMap_bijective_at_image_of_endpoint
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (n : ℕ)
    (hπ : Function.Bijective (HomotopyGroup.piMap n f h)) :
    Function.Bijective (HomotopyGroup.piMap n f (x := x) rfl) := by
  cases h
  exact hπ

/-- Twisted homology recognizes the actual map using a single supplied
simply connected target cover and one matching pair. -/
theorem isWeakHomotopyEquivalence_of_twisted_quasiIso_of_cover
    {X Y E : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
    [PathConnectedSpace X] [PathConnectedSpace Y] [SimplyConnectedSpace E]
    (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
    (x : X) (e : E) (h : f x = q e)
    (hπ : Function.Bijective (HomotopyGroup.piMap 0 f (x := x) rfl))
    (hH : ∀ A : FundamentalGroupoid.LocalCoefficients.System.{u, u} Y,
      QuasiIso (FundamentalGroupoid.LocalCoefficients.UniverseLift.chainMap.{u, u, u} f A)) :
    IsWeakHomotopyEquivalence f := by
  let z₀ : Covering.Pullback.Space f q := ⟨(x, e), h⟩
  let : SimplyConnectedSpace (Covering.Pullback.Space f q) :=
    Covering.Pullback.simplyConnectedSpace f q hq z₀ hπ
  have hsing := pullback_singular_quasiIso_of_all_localCoefficients hq f hH
  have hweak : IsWeakHomotopyEquivalence (Covering.Pullback.lift f q) :=
    isWeakHomotopyEquivalence_of_singular_quasiIso _ hsing
  apply isWeakHomotopyEquivalence_of_connected f x
  intro n
  cases n with
  | zero => exact hπ
  | succ m =>
    exact piMap_bijective_at_image_of_endpoint f h (m + 1)
      (Covering.Pullback.piMap_base_bijective_of_lift f q hq z₀ m
        (hweak.homotopy_bijective z₀ (m + 2)))

end Topology.LocalCoefficients
