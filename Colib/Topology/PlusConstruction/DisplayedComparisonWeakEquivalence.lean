/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.PullbackWeakEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceConnected
public import Colib.Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected
public import Colib.Topology.PlusConstruction.DisplayedComparisonCover

/-!
# A displayed plus comparison detected by a simply connected covering

For the original comparison under the source, the supplied simply connected
target covering and chosen point give a simply connected literal pullback.
Local-coefficient preservation is applied to its actual covering-fiber
coefficient system. Homological Whitehead detects weakness upstairs, and
covering projections descend higher groups to the original comparison.
No independent source covering, comparison inverse or CW structure is assumed.

The descent step specializes the supplied-cover argument of
`Quillen/Topology/LocalCoefficients/TwistedWhiteheadSuppliedCovers.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

universe u
open CategoryTheory FundamentalGroupoid
open scoped Topology

namespace Topology.IsPlusConstruction

private theorem piMap_bijective_at_image_of_endpoint
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (k : C(Y, Z)) {y : Y} {z : Z} (hz : k y = z) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.piMap n k hz)) :
    Function.Bijective (HomotopyGroup.piMap n k (x := y) rfl) := by
  cases hz
  exact h

/-- The actual displayed comparison between two plus maps with the same
marked kernel is a weak equivalence if its target has the indicated simply
connected covering at the comparison of the marked point. -/
theorem displayedComparison_isWeakHomotopyEquivalence_of_cover
    {X Y Z E : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace E] [SimplyConnectedSpace E]
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    (q : C(E, Z)) (hq : IsCoveringMap q) (e : E) (he : k y = q e) :
    IsWeakHomotopyEquivalence k := by
  let : PathConnectedSpace Y := hf.targetPathConnected
  let : PathConnectedSpace Z := hg.targetPathConnected
  obtain ⟨hsc, hH⟩ :=
    displayedComparison_simplyConnected_pullback_singular_quasiIso f g k H γ δ N hf hg q hq e he
  let : SimplyConnectedSpace (Covering.Pullback.Space k q) := hsc
  have hweak : IsWeakHomotopyEquivalence (Covering.Pullback.lift k q) :=
    LocalCoefficients.isWeakHomotopyEquivalence_of_singular_quasiIso _ hH
  let z₀ : Covering.Pullback.Space k q := ⟨(y, e), he⟩
  apply isWeakHomotopyEquivalence_of_connected k y
  intro n
  cases n with
  | zero => exact displayedComparison_piOne_bijective f g k H γ δ N hf hg
  | succ m =>
    exact piMap_bijective_at_image_of_endpoint k he (m + 1)
      (Covering.Pullback.piMap_base_bijective_of_lift k q hq z₀ m
        (hweak.homotopy_bijective z₀ (m + 2)))

end Topology.IsPlusConstruction
