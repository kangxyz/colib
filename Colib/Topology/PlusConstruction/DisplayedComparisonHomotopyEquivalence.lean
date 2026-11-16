/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.Whitehead
public import Colib.Topology.PlusConstruction.DisplayedComparisonWeakEquivalence

/-!
# A homotopy inverse to the original displayed plus comparison

A supplied simply connected target covering detects the weak equivalence of
the original comparison. For actual Hausdorff classical CW subtypes, CW
Whitehead constructs an inverse to this same map with both homotopies. The
marked kernel, under-source homotopy, and covering lift are the original data.
This neither constructs a comparison nor proves uniqueness of its homotopy
class.

This is the classical CW analogue of the supplied-cover realization result in
`Quillen/Topology/PlusConstruction/DisplayedComparisonRealizations.lean:30-60`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Set
open scoped Topology
universe u

namespace Topology.IsPlusConstruction

variable {X Y Z E : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Z] [T2Space Z] [TopologicalSpace E] [SimplyConnectedSpace E]
  (C : Set Y) (D : Set Z) [CWComplex C] [CWComplex D]
  (f : C(X, C)) (g : C(X, D)) (k : C(C, D)) (H : (k.comp f).Homotopy g)
  {x : X} {y : C} {z : D} (γ : Path (f x) y) (δ : Path (g x) z)
  (N : Subgroup (HomotopyGroup.Pi 1 X x))
  (hf : IsPlusConstruction.{u, u, u} f γ N) (hg : IsPlusConstruction.{u, u, u} g δ N)
  (q : C(E, D)) (hq : IsCoveringMap q) (e : E) (he : k y = q e)

/-- CW Whitehead recognizes the literal displayed comparison, using only a
supplied simply connected covering of its target and the chosen marked lift. -/
noncomputable def displayedComparisonHomotopyEquivOfCover :
    ContinuousMap.HomotopyEquiv C D :=
  CWComplex.homotopyEquivOfWeakHomotopyEquivalence C D k
    (displayedComparison_isWeakHomotopyEquivalence_of_cover f g k H γ δ N hf hg q hq e he)

/-- The forward map of the constructed homotopy equivalence is the original comparison. -/
theorem displayedComparisonHomotopyEquivOfCover_toFun :
    (displayedComparisonHomotopyEquivOfCover C D f g k H γ δ N hf hg q hq e he).toFun = k := rfl

/-- One inverse to the original comparison carries both original-map inverse homotopies. -/
theorem displayedComparison_exists_inverse_homotopies_of_cover :
    ∃ l : C(D, C),
      Nonempty ((l.comp k).Homotopy (ContinuousMap.id C)) ∧
        Nonempty ((k.comp l).Homotopy (ContinuousMap.id D)) := by
  let a := displayedComparisonHomotopyEquivOfCover C D f g k H γ δ N hf hg q hq e he
  exact ⟨a.invFun, a.left_inv, a.right_inv⟩

end Topology.IsPlusConstruction
