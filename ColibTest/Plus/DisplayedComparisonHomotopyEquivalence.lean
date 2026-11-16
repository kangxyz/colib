module

public import Colib.Topology.PlusConstruction.DisplayedComparisonHomotopyEquivalence

set_option autoImplicit false

open Set Topology Topology.IsPlusConstruction
open scoped Topology unitInterval

universe u

variable {X Y Z E : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Z] [T2Space Z] [TopologicalSpace E] [SimplyConnectedSpace E]
  (C : Set Y) (D : Set Z) [CWComplex C] [CWComplex D]
  (f : C(X, C)) (g : C(X, D)) (k : C(C, D)) (H : (k.comp f).Homotopy g)
  {x : X} {y : C} {z : D} (γ : Path (f x) y) (δ : Path (g x) z)
  (N : Subgroup (HomotopyGroup.Pi 1 X x))
  (hf : IsPlusConstruction.{u, u, u} f γ N) (hg : IsPlusConstruction.{u, u, u} g δ N)
  (q : C(E, D)) (hq : IsCoveringMap q) (e : E) (he : k y = q e)

-- The inverse data has precisely the comparison as its forward map at every point.
example (c : C) :
    (displayedComparisonHomotopyEquivOfCover C D f g k H γ δ N hf hg q hq e he).toFun c =
      k c :=
  ContinuousMap.congr_fun
    (displayedComparisonHomotopyEquivOfCover_toFun C D f g k H γ δ N hf hg q hq e he) c

-- The same inverse has actual tracks between the specified endpoints at all points.
example :
    ∃ (l : C(D, C)) (hl : (l.comp k).Homotopy (ContinuousMap.id C))
      (hr : (k.comp l).Homotopy (ContinuousMap.id D)),
      (∀ c : C, hl (0, c) = l (k c) ∧ hl (1, c) = c) ∧
        (∀ d : D, hr (0, d) = k (l d) ∧ hr (1, d) = d) := by
  obtain ⟨l, ⟨hl⟩, ⟨hr⟩⟩ :=
    displayedComparison_exists_inverse_homotopies_of_cover C D f g k H γ δ N hf hg q hq e he
  exact ⟨l, hl, hr, fun c ↦ ⟨hl.map_zero_left c, hl.map_one_left c⟩,
    fun d ↦ ⟨hr.map_zero_left d, hr.map_one_left d⟩⟩

#print axioms displayedComparisonHomotopyEquivOfCover
#print axioms displayedComparison_exists_inverse_homotopies_of_cover
